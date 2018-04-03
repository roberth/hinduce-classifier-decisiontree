-- |
--
-- Decision tree learning, used in statistics, data mining and machine
-- learning, uses a decision tree as a predictive model which maps
-- observations about an item to conclusions about the item's target
-- value. In these tree structures, leaves represent class labels and
-- branches represent conjunctions of features that lead to those
-- class labels.
--
-- In data mining, a decision tree describes data but not decisions;
-- rather the resulting classification tree can be an input for
-- decision making.
--
-- (<https://en.wikipedia.org/wiki/Decision_tree_learning>,
-- Dec 6 2011)

-- TODO: 'interactive' example

module Data.HInduce.Classifier.DecisionTree 
       ( -- * Decision Tree
         DTree(..)
       , DTreeAlgebra(..)
       , buildDTree
       , foldD
       , toDot
         -- * Deciders
       , Decider(..)
       , DecideOrd(..)
       , DecideSet(..)
       , AutoDecide(..)
         -- * Composing @Decider@s
         --
         -- | Though @autoDeciders@ may provide good results, deciders
         -- may be out there that do not get generated. These
         -- functions let deviate from autoDeciders and compose very
         -- specific deciders.
       , genOrds
       , genOrdsAvg
       , genPair
       , genMany
       , avgF, avgI
       -- , genEq -- TODO not of sufficient quality to export now
       ) where
import Data.Convertible
import Data.HInduce.Classifier
import Data.List
import Data.List.HIUtils
import Data.Maybe
import Data.Ord
import Data.Ratio
import Control.Arrow
import Text.Layout
import Text.Layout.DisplayText
import Text.Layout.DisplayLatex

-- | @decide@ defines the type and semantics of a split. For example,
-- the split \"attr <= 20\" is created by @DecideOrd 20@.
--
-- For every possible value of type @branch@, an actual tree branch
-- may be created. Allowing many distinct values in @branch@ is a bad
-- idea. Too many of these may have little predictive value and
-- exhaust the training database more quickly.
--
-- @decider@: The representation of the decider
-- @attr@: The data it needs
-- @branch@: The key of that leads to a branch
class Decider decider attr branch | decider -> attr branch where
    -- | Distinguish values of type @attr@ using @decider@.
    decide :: decider -> attr -> branch

-- | Decide with Ord
data (Ord t) => DecideOrd t = DecideOrd t
     deriving (Show, Read)
              
-- | Decide with set ([]) membership, requiring Eq
data (Eq t) => DecideSet t = DecideSet [t]
     deriving (Show, Read)

-- | Decider with index for use with lists
data Ixd decider = decider :!! Int
     deriving (Show, Read)

instance (Ord attr) => Decider (DecideOrd attr) attr Bool where
    decide (DecideOrd pivot) = (<= pivot)
        -- <= is easier than < in presence of round-down

instance (Eq attr) => Decider (DecideSet attr) attr Bool where
    decide (DecideSet set) = (`elem` set)

instance (Decider decider attr branch) => Decider (Ixd decider) [attr] branch where
    decide (decider :!! i) = decide decider . (!! i)

instance (Decider deca attra branch, Decider decb attrb branch) =>
          Decider (Either deca decb) (attra, attrb) branch where
    decide (Left dec) = decide dec . fst
    decide (Right dec) = decide dec . snd

-- | Concept of a decider generator. Not actually used in the code because it would obfuscate a simple computation.
type DeciderGenerator attr decider = [attr] -> [decider]

-- | @AutoDecide@ is used to generate possible splits based on actual
-- attributes, in a straightforward fashion. Think of AutoDecide as a
-- default implementation for @Decider@ generation.
class AutoDecide attr decider | attr -> decider where
    autoDeciders :: [attr] -> [decider]

-- | Decider generator implementation for any ordered data; considers all sensible @(<= pivot)@s.
genOrds :: (Ord attr) => [attr] -> [DecideOrd attr]
genOrds window = map DecideOrd $ filter (/= maximum window) window

-- | Decider generator for any ordered data; considers all possible @(<= pivot)@s.
genOrdsAvg :: (Ord attr) => (attr -> attr -> attr) -> [attr] -> [DecideOrd attr]
genOrdsAvg favg window = map DecideOrd $ zipWith favg window' (tail window')
        where window' = uniqSort window

-- | Decider generator for any categorical data; considers all possible sets.
genEq :: (Ord attr) => [attr] -> [DecideSet attr]
genEq window = map DecideSet $ subsequences {- ;) -} $ uniqSort window

genPair :: DeciderGenerator attra decidera
                 -> DeciderGenerator attrb deciderb 
                 -> DeciderGenerator (attra, attrb) (Either decidera deciderb)
genPair p q v = (map Left . p . map fst) v ++ (map Right . q . map snd) v

genMany :: DeciderGenerator attr decider
                 -> DeciderGenerator [attr] (Ixd decider)
genMany d window = 
  if not $ all (== length (head window)) $ map length window
  then error "Refusing to generate deciders for variable length list attribute"
  else [d' :!! i | i <- [0 .. (length$ head window)-1]
                 , d' <- d (map (!! i) window)]

-- | @avgF a b = (a+b) / 2@, to be used with genOrdsAvg
avgF :: (Fractional a) => a -> a -> a
avgF a b = (a+b) / 2

-- | @avgI a b = (a+b) `div` 2@, to be used with genOrdsAvg
avgI :: (Integral a) => a -> a -> a
avgI a b = (a+b) `div` 2

instance AutoDecide Double (DecideOrd Double) where autoDeciders = genOrdsAvg avgF
instance AutoDecide Float (DecideOrd Float) where autoDeciders = genOrdsAvg avgF
instance AutoDecide Int (DecideOrd Int) where autoDeciders = genOrdsAvg avgI
instance AutoDecide Integer (DecideOrd Integer) where autoDeciders = genOrdsAvg avgI
instance (Integral a) => AutoDecide (Ratio a) (DecideOrd (Ratio a)) where autoDeciders = genOrdsAvg avgF

instance AutoDecide Char (DecideSet Char) where autoDeciders = genEq
instance AutoDecide [Char] (DecideSet [Char]) where autoDeciders = genEq

instance (AutoDecide a xa, AutoDecide b xb) =>
          AutoDecide (a,b) (Either xa xb)
  where autoDeciders = genPair autoDeciders autoDeciders {- (map Left . autoDeciders . map fst) v ++
                  (map Right . autoDeciders . map snd) v -}

{-
Note: this does not work because of FunDep in Decider
Every n-tuple type needs a new Either-like type with n constructors.
It's sad.

instance ( AutoDecide a xa
         , AutoDecide b xb
         , AutoDecide c xc
         ) =>
          AutoDecide (a, b, c) (Either xa (Either xb xc))
  where autoDeciders = autoDeciders . map (\(a, b, c) -> (a, (b, c)))
-}

doSplit :: (Decider decider attr branch, Ord branch) =>
     (x -> attr) -> decider -> [x] -> [(branch, [x])]
doSplit toattr dec = aggregateAL . map ((decide dec . toattr) &&& id)

doLabel :: (Ord label) => (x -> label) -> [x] -> [(label, [x])]
doLabel tolabel = aggregateAL . map (tolabel &&& id)

measureImpurity :: (Ord label) => (attr -> label) -> [(branch, [attr])] -> Double
measureImpurity tolabel = f . impurityAndCounts
  where f :: [(Double, Int)] -> Double
        f = sum . map (uncurry (*) . second fromIntegral)
        impu = gini . map (length . snd) . doLabel tolabel
        impurityAndCounts = map ((impu &&& length) . snd)

-- | Calculate the gini impurity based on the real class label frequencies.
gini :: (Integral i, Fractional f) => [i] -> f
gini = sum . map (\x -> x * (1 - x)) . relFreq

rateSplits :: (Decider decider attr branch,
              Ord branch, Ord label) => 
              DeciderGenerator attr decider ->
              (x -> attr) ->
              (x -> label) ->
              [x] ->
              [(decider, Double)]
rateSplits decGen toattr tolabel window = map (\dec -> (dec,) $ measureImpurity tolabel $ doSplit toattr dec window) . decGen . map toattr $ window

-- | A decision tree data structure that allows arbitrary numbers of
-- children.  It has been proven that a binary tree is equally
-- expressive, but considering that decision trees are a 'white box'
-- model, we do not want to limit ourselves to the binary case because
-- other numbers of children may make more sense to humans.
--
-- Converting between binary and arbitrary-child trees is feasible though,
-- but probably not very interesting.

data DTree decider branch label = Node { dDecider :: decider
                                       , dChildren :: [(branch, DTree decider branch label)]
                                       }
                                | Leaf { dLabel :: label 
                                       }
                                deriving (Show, Eq)

-- | An algebra on decision trees
data DTreeAlgebra decider branch label a =
  DTreeAlgebra { fleaf :: label -> a
               , fnode :: decider -> [(branch, a)] -> a
               }

-- | fold on a DTree
foldD :: DTreeAlgebra dec branch label a -> DTree dec branch label -> a
foldD (DTreeAlgebra fleaf _) (Leaf label) = fleaf label
foldD a@(DTreeAlgebra _ fnode) (Node dec children) = fnode dec $ map (second (foldD a)) children

-- | Prediction is
predictAlgebra :: (Decider dec attr branch, Eq branch) =>
                  attr -> DTreeAlgebra dec branch label label
predictAlgebra newobservation = DTreeAlgebra { fleaf = fleaf, fnode = fnode }
 where
   fleaf = id
   fnode dec children = error "Incomplete tree"
           `fromMaybe` lookup (decide dec newobservation) children

-- | Use a DTree to predict the class label of a (possibly) yet unseen object.
-- Library users: use @classify@.
predict :: (Decider dec attr branch, Eq branch) =>
           attr -> DTree dec branch a -> a
predict a = foldD (predictAlgebra a)

instance (Decider decider attr branch, Eq branch) => Classifier (DTree decider branch label) attr label where
  classify = flip predict

-- | Learn a Decision Tree classifier based on a list of observations.
buildDTree' :: (Ord label, Ord branch,
      AutoDecide attr dec,
      Decider dec attr branch) =>
     (x -> attr) ->
     (x -> label) ->
     [x] ->
     DTree dec branch label
buildDTree' = buildDTree autoDeciders
  
buildDTree :: (Ord label, Ord branch, Decider decider attr branch) =>
              DeciderGenerator attr decider -> 
              (x -> attr) ->
              (x -> label) ->
              [x] ->
              DTree decider branch label
buildDTree decGen toAttr toLabel window = case rateSplits decGen toAttr toLabel window of
  [] -> case window of
    [] -> error "Empty window"
    window -> Leaf . majority . map toLabel $ window
  splits -> case uniqSort (map toLabel window) of
    [x] -> Leaf x
    _ -> let 
            (best, _) = minimumBy (comparing snd) splits
            subwins = doSplit toAttr best window
        in Node best $ map (second (buildDTree decGen toAttr toLabel)) subwins


-- Rendering --

-- | Render a decision tree to Graphviz Dot format.
toDot :: (Show decider, Show branch, Show label) =>
         DTree decider branch label -> String
toDot t = "digraph G {\n" ++
          foldD (DTreeAlgebra { fleaf = fleaf, fnode = fnode }) t "dtree" ++
          "}\n"
  where
    fleaf label  pfx = pfx++" [label="++show (show label)++"];\n"
    fnode dec cs pfx = pfx++" [label="++show (show dec)++" shape=plaintext];\n"++
                       ((concatMap (\(n, (key, f)) ->
                                     let newpfx = pfx ++ "_c"++show n
                                     in pfx++" -> " ++ newpfx ++
                                        "[label="++show (show key)++"];\n" ++
                                        f newpfx
                                   )
                         $ zip nat0 cs) :: String)

instance (Show decider, Show branch, Show label) => 
         Convertible (DTree decider branch label) DisplayText where
  safeConvert = Right . DisplayText . printTree 0
    where 
      spcs = flip replicate ' '
      printTree indent Node {dDecider=dec,dChildren=children} =
            spcs indent ++ "Node " ++ show dec ++ "\n" ++
            concatMap (\(k, v) -> spcs (indent+2) ++ show k ++ "\n" ++
                       printTree (indent + 4) v)
                children
      printTree indent Leaf {dLabel=label} =
            spcs indent ++ "Leaf " ++ show label ++ "\n"

instance (Show decider, Show branch, Show label) => 
         Convertible (DTree decider branch label) DisplayLatex where
  safeConvert t = Right $ DisplayLatex $ "\\begin{tikzpicture}\n\\" ++
                  (printTree 0 "" t) ++ ";\\end{tikzpicture}\n"
    where
      spcs = flip replicate ' '
      --printTree :: Int -> String -> DTree dec branch label -> String
      printTree indent key Node {dChildren=children, dDecider=dec} =
        spcs indent ++ "node{" ++ key ++ show dec ++ "}\n" ++
        concatMap (\(k, v) -> "child {\n" ++ 
                              printTree (indent + 4) (show k++"\\\\\n") v ++
                              "}\n"
                  ) children ++
        "\n"
      printTree indent key Leaf {dLabel=label} =
        spcs indent ++ "\\node {" ++ show label ++ "}\n"
