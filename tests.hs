module Tests where

import Control.Monad
import Data.Maybe

--import TreeZipper
import TreeZipper2
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
test2 =  (enter >>> goDown) >=> (goRight >=> goDown >=> goRight)
               >=> (update (\_ -> Leaf 666) >>> leave >>> return) $ tree

test3 :: Maybe (Tree Int Bool)
test3 =  enter >>> goDown >=> goRight >=> goRight >=> goDown >=> goRight
               >=> goUp >=> update (\_ -> Leaf 13)
     >>> leave >>> return $ tree

test4 :: Maybe (Tree Int Bool)
test4 =  enter >>> goDown >=> goRight >=> goRight >=> goDown >=> goDown
    >=> leave >>> return $ tree

-- Print the results of tests
runTests :: IO ()
runTests = do
    print $ from tree
    print $ fromJust test1
    print $ fromJust test2
    print $ fromJust test3
    print $ fromJust test4
