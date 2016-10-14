{-# LANGUAGE TypeOperators, TypeFamilies #-}
module Tests where

import Control.Monad
import Data.Maybe

import Zipper
import Regular

-- An example of a datatype: Tree
data Tree a b = Leaf a
              | TNode (Tree a b) (Tree a b) a b (Tree a b)
              | BNode b (Tree a b) (Tree a b)

-- A Regular instance
instance Regular (Tree a b) where
    type PF (Tree a b) = K a
                     :+: I :*: I :*: K a :*: K b :*: I
                     :+: K b :*: I :*: I

    from (Leaf x)          = L (K x)
    from (TNode l m x y r) = R (L (I l :*: I m :*: K x :*: K y :*: I r))
    from (BNode x l r)     = R (R (K x :*: I l :*: I r))

    to (L (K x))                                     = Leaf x
    to (R (L (I l :*: I m :*: K x :*: K y :*: I r))) = TNode l m x y r
    to (R (R (K x :*: I l :*: I r)))                 = BNode x l r

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

-- An example value of Tree
tree :: Tree Int Bool
tree =  TNode (Leaf 13)
              (TNode (Leaf 15) (Leaf 24) 16 True (Leaf 10))
              11
              False
              (BNode False (Leaf 13) (BNode True
                                           (Leaf 33)
                                           (Leaf  9)))

-- ------------------------ Testing
test1 :: Maybe (Tree Int Bool)
test1 =  enter >>> goDown >=> update (\_ -> Leaf 42)
     >>> leave >>> return $ tree

test2 :: Maybe (Tree Int Bool)
test2 =  enter >>> goDown >=> goRight >=> goDown >=> goRight >=> goLeft
               >=> update (\_ -> Leaf 666) >>> leave >>> return $ tree

test3 :: Maybe (Tree Int Bool)
test3 =  enter >>> goDown >=> goRight >=> goRight >=> goDown >=> goRight
               >=> goUp >=> update (\_ -> Leaf 13)
     >>> leave >>> return $ tree

-- Print the results of tests
runTests :: IO ()
runTests = do
    print $ fromJust test1
    print $ fromJust test2
    print $ fromJust test3
