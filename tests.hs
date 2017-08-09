{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds,
    UndecidableInstances, FlexibleInstances, PolyKinds,
    ConstraintKinds, ScopedTypeVariables #-}
module Tests where

import Control.Monad
import Data.Maybe

import GHC.Exts (Constraint)
import TreeZipper
import Generics.SOP

-- A Show instance
instance (Show a, Show b) => Show (Tree a b) where
    show (Leaf x)          = "|" ++ show x ++ "|"
    show (TNode l m x y r) = "(" ++ show l ++
                             " " ++ show m ++
                             " " ++ show x ++
                             " " ++ show y ++
                             " " ++ show r ++ ")"
    show (BNode x l r)     = "(" ++ show x ++
                             " " ++ show l ++
                             " " ++ show r ++ ")"

type TreeIB = Tree Int Bool

-- An example value of Tree
tree :: TreeIB
tree =  TNode (Leaf 13)
              (TNode (Leaf 15) (Leaf 24) 16 True (Leaf 10))
              11
              False
              (BNode False (Leaf 13) (BNode True
                                           (Leaf 33)
                                           (Leaf  9)))

tree2 :: TreeIB
tree2 = BNode True (Leaf 42) (Leaf 35)

-- ------------------------ Type Pattern Matching
class Indexed a where
   index :: proxy a -> Integer

instance Indexed 'False where
   index _ = 0
instance Indexed 'True where
   index _ = 1

{-type family Check a b :: Bool where
   Check a a = 'True
   Check a x = 'False-}

type family AllIndexedTree (xs :: [k]) :: Constraint where
   AllIndexedTree '[]       = ()
   AllIndexedTree (x ': xs) = (Indexed (Check TreeIB x), AllIndexedTree xs)

type family All2IndexedTree (xss :: [[k]]) :: Constraint where
    All2IndexedTree '[]         = ()
    All2IndexedTree (xs ': xss) = (AllIndexedTree xs, All2IndexedTree xss)

testPM :: (Generic a, All2IndexedTree (Code a)) => a -> Integer
testPM t = testPM_NS (unSOP $ from t)

testPM_NS :: All2IndexedTree xss => NS (NP I) xss -> Integer
testPM_NS (S ns) = testPM_NS ns
testPM_NS (Z np) = testPM_NP np

testPM_NP :: AllIndexedTree xs => NP I xs -> Integer
testPM_NP (I (_ :: a) :* _) = index (Proxy :: Proxy (Check TreeIB a))
testPM_NP Nil               = impossible

-- ------------------------ Testing
test1 :: Maybe TreeIB
test1 =  enter >>> goDown >=> update (\_ -> Leaf 42)
     >>> leave >>> return $ tree

test2 :: Maybe TreeIB
test2 =  (enter >>> goDown) >=> (goRight >=> goDown >=> goRight)
               >=> (update (\_ -> Leaf 666) >>> leave >>> return) $ tree

test3 :: Maybe TreeIB
test3 =  enter >>> goDown >=> goRight >=> goRight >=> goDown >=> goRight
               >=> goUp >=> update (\_ -> Leaf 13)
     >>> leave >>> return $ tree

test4 :: Maybe TreeIB
test4 =  enter >>> goDown >=> goRight >=> goRight >=> goDown >=> goDown
    >=> leave >>> return $ tree

testPM1 :: Integer
testPM1 = testPM tree

testPM2 :: Integer
testPM2 = testPM tree2

-- Print the results of tests
runTests :: IO ()
runTests = do
    print $ from tree
    print $ fromJust test1
    print $ fromJust test2
    print $ fromJust test3
--    print $ fromJust test4
    print testPM1 -- 1
    print testPM2 -- 0
