{-# LANGUAGE DeriveGeneric, DataKinds #-}
module TreeExample where

import Generics.SOP
import qualified GHC.Generics as GHC (Generic)

import GenericContext

-- An example of a datatype: Tree
data Tree a b = Leaf a
              | TNode (Tree a b) (Tree a b) a b (Tree a b)
              | BNode b (Tree a b) (Tree a b)
    deriving GHC.Generic

data MutTree1 a b = Leaf1 a
                  | TNode1 (MutTree1 a b) (MutTree2 a b) a b (MutTree1 a b)
                  | BNode1 b (MutTree2 a b) (MutTree1 a b)
    deriving GHC.Generic

data MutTree2 a b = Leaf2 a
                  | TNode2 (MutTree2 a b) (MutTree1 a b) a b (MutTree2 a b)
                  | BNode2 b (MutTree1 a b) (MutTree2 a b)
    deriving GHC.Generic

instance Generic (Tree a b)
instance Generic (MutTree1 a b)
instance Generic (MutTree2 a b)

type TreeIB = Tree Int Bool
type MutTreeIB1 = MutTree1 Int Bool
type MutTreeIB2 = MutTree2 Int Bool

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

instance (Show a, Show b) => Show (MutTree1 a b) where
   show (Leaf1 x)          = "|" ++ show x ++ "|"
   show (TNode1 l m x y r) = "(" ++ show l ++
                             " " ++ show m ++
                             " " ++ show x ++
                             " " ++ show y ++
                             " " ++ show r ++ ")"
   show (BNode1 x l r)     = "(" ++ show x ++
                             " " ++ show l ++
                             " " ++ show r ++ ")"

instance (Show a, Show b) => Show (MutTree2 a b) where
   show (Leaf2 x)          = "|" ++ show x ++ "|"
   show (TNode2 l m x y r) = "(" ++ show l ++
                             " " ++ show m ++
                             " " ++ show x ++
                             " " ++ show y ++
                             " " ++ show r ++ ")"
   show (BNode2 x l r)     = "(" ++ show x ++
                             " " ++ show l ++
                             " " ++ show r ++ ")"

type P2 = Proxy ('N 'F)
type P3 = Proxy ('N ('N 'F))

data TreeCtx a b = TNode_1 P2 Hole (Tree a b) a b (Tree a b)
                 | TNode_2 P2 (Tree a b) Hole a b (Tree a b)
                 | TNode_3 P2 (Tree a b) (Tree a b) a b Hole
                 | BNode_1 P3 b Hole (Tree a b)
                 | BNode_2 P3 b (Tree a b) Hole
    deriving GHC.Generic

instance Generic (TreeCtx a b)
