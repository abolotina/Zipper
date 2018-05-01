{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds,
    UndecidableInstances, FlexibleInstances, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, MultiParamTypeClasses,
    FlexibleContexts, UndecidableSuperClasses, TypeApplications,
    Rank2Types #-}
module Main where

import GHC.Exts (Constraint)
import Data.Maybe
import Control.Monad ((>=>))

import qualified DiffTests
import TreeExample
import Generics.Zipper.GenericZipper
import Generics.Zipper.Base

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

leaf1 :: Int -> MutTreeIB1
leaf1 = Leaf1

leaf2 :: Int -> MutTreeIB2
leaf2 = Leaf2

-- An example value of MutTree1
mutTree :: MutTreeIB1
mutTree = TNode1 (Leaf1 13)
                 (TNode2 (leaf2 15) (leaf1 24) 16 True (leaf2 10))
                 11
                 False
                 (BNode1 False (leaf2 13) (BNode1 True
                                                  (leaf2 33)
                                                  (Leaf1 9)))

np1 :: NP I '[TreeIB, TreeIB, Int, Bool, TreeIB]
np1 = I (Leaf 1) :* I (Leaf 2) :* I 1 :* I True :* I (Leaf 3) :* Nil

np2 :: NP I '[TreeIB, TreeIB, Int, Int, TreeIB]
np2 = I (Leaf 1) :* I (Leaf 2) :* I 1 :* I 2 :* I (Leaf 3) :* Nil

-------------------------------------------------
--                          Type Pattern Matching
-------------------------------------------------
-- ------------------------ Type pattern matching: test 1
class Indexed a where
   index :: proxy a -> Integer

instance Indexed 'False where
   index _ = 0
instance Indexed 'True where
   index _ = 1

{-type family Equal a b :: Bool where
   Equal a a = 'True
   Equal a x = 'False-}

type family AllIndexedTree (xs :: [k]) :: Constraint where
   AllIndexedTree '[]       = ()
   AllIndexedTree (x ': xs) = (Indexed (Equal TreeIB x), AllIndexedTree xs)

type family All2IndexedTree (xss :: [[k]]) :: Constraint where
    All2IndexedTree '[]         = ()
    All2IndexedTree (xs ': xss) = (AllIndexedTree xs, All2IndexedTree xss)

testPM :: (Generic a, All2IndexedTree (Code a)) => a -> Integer
testPM t = testPM_NS (unSOP $ from t)

testPM_NS :: All2IndexedTree xss => NS (NP I) xss -> Integer
testPM_NS (S ns) = testPM_NS ns
testPM_NS (Z np) = testPM_NP np

testPM_NP :: AllIndexedTree xs => NP I xs -> Integer
testPM_NP (I (_ :: a) :* _) = index (Proxy :: Proxy (Equal TreeIB a))
testPM_NP Nil               = impossible

testPM1 :: Integer
testPM1 = testPM tree

testPM2 :: Integer
testPM2 = testPM tree2

-- ------------------------ Type pattern matching: test 2
class Boolean (b :: Bool) where
    bool :: Proxy b -> Bool
instance Boolean 'True where
    bool _ = True
instance Boolean 'False where
    bool _ = False

type family AllBoolEq (xs :: [k]) (ys :: [k]) :: Constraint where
    AllBoolEq  xs       '[]       = ()
    AllBoolEq '[]        ys       = ()
    AllBoolEq (x ': xs) (y ': ys) = (Boolean (Equal x y), AllBoolEq xs  ys)

type family All2BoolEq (xs :: [k]) (yss :: [[k]]) :: Constraint where
    All2BoolEq  xs '[]         = ()
    All2BoolEq  xs (ys ': yss) = (AllBoolEq xs ys, All2BoolEq xs yss)

testBool :: (Generic a, All2BoolEq xs (Code a))
    => NP I xs -> a -> Bool
testBool xs t = testBoolNS xs (unSOP $ from t)

testBoolNS :: All2BoolEq xs yss
    => NP I xs -> NS (NP I) yss -> Bool
testBoolNS np (S ns)  = testBoolNS np ns
testBoolNS np (Z np') = testBoolNP np np'

testBoolNP :: AllBoolEq xs ys => NP I xs -> NP I ys -> Bool
testBoolNP (I (_ :: a) :* xs) (I (_ :: b) :* ys)
    = bool (Proxy :: Proxy (Equal a b)) && testBoolNP xs ys
testBoolNP Nil Nil = True
testBoolNP _   _   = False

testBool1 :: Bool
testBool1 = testBool np1 tree

testBool2 :: Bool
testBool2 = testBool np2 tree

-------------------------------------------------
--                                 Generic Zipper
-------------------------------------------------
-- ------------------------ Testing
class UpdateTree a where
    change :: TreeIB -> a -> a
instance UpdateTree TreeIB where
    change t _ = t

type TreeFam = '[TreeIB]

test1 :: Maybe TreeIB
test1 =  enter @TreeFam @UpdateTree
             >>> goDown >=> update (change $ Leaf 42)
             >>> leave >>> return $ tree

test2 :: Maybe TreeIB
test2 =  enter @TreeFam @UpdateTree
             >>> goDown >=> goRight >=> goDown >=> goRight
             >=> update (change $ Leaf 666)
             >>> leave >>> return $ tree

test3 :: Maybe TreeIB
test3 =  enter @TreeFam @UpdateTree
             >>> goDown >=> update (change $ Leaf 13)
             >>> leave >>> return $ tree2

test4 :: Maybe TreeIB
test4 =  enter @TreeFam @UpdateTree
             >>> goDown >=> goRight >=> goRight
             >=> goDown >=> goRight >=> goUp
             >=> update (change $ Leaf 18)
             >>> leave >>> return $ tree

test5 :: Maybe TreeIB
test5 =  enter @TreeFam @UpdateTree
             >>> goDown >=> goRight >=> goRight
             >=> goDown >=> goDown
             >=> leave >>> return $ tree

-------------------------------------------------
--                   Mutually Recursive Datatypes
-------------------------------------------------
class UpdateInt a where
    changeInt :: Int -> a -> a
instance UpdateInt MutTreeIB1 where
    changeInt x _ = Leaf1 x
instance UpdateInt MutTreeIB2 where
    changeInt x _ = Leaf2 x

type MutTreeFam = '[MutTreeIB1, MutTreeIB2]

mutTest1 :: Maybe MutTreeIB1
mutTest1 =  enter @MutTreeFam @UpdateInt
             >>> goDown >=> update (changeInt 42)
             >>> leave >>> return $ mutTree

mutTest2 :: Maybe MutTreeIB1
mutTest2 =  enter @MutTreeFam @UpdateInt
             >>> goDown >=> goRight >=> goDown >=> goRight
             >=> update (changeInt 666)
             >>> leave >>> return $ mutTree

mutTest3 :: Maybe MutTreeIB1
mutTest3 =  enter @MutTreeFam @UpdateInt
             >>> goDown >=> goRight >=> goRight
             >=> goDown >=> goRight >=> goUp
             >=> update (changeInt 18)
             >>> leave >>> return $ mutTree

mutTest4 :: Maybe MutTreeIB1
mutTest4 =  enter @MutTreeFam @UpdateInt
             >>> goDown >=> goRight >=> goRight
             >=> goDown >=> goDown
             >=> leave >>> return $ mutTree

-------------------------------------------------
-- Print the results of tests
runTests :: IO ()
runTests = do
    print $ from tree
    print $ fromJust test1
    print $ fromJust test2
    print $ fromJust test3
    print $ fromJust test4
--    print $ fromJust test5
    print $ fromJust mutTest1
    print $ fromJust mutTest2
    print $ fromJust mutTest3
--    print $ fromJust mutTest4
    print testPM1   -- 1
    print testPM2   -- 0
    print testBool1 -- True
    print testBool2 -- False

main :: IO ()
main = runTests
