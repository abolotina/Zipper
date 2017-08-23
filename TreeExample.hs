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

type TreeIB = Tree Int Bool

type P2 = Proxy ('N 'F)
type P3 = Proxy ('N ('N 'F))

data TreeCtx a b = TNode1 P2 Hole (Tree a b) a b (Tree a b)
                 | TNode2 P2 (Tree a b) Hole a b (Tree a b)
                 | TNode3 P2 (Tree a b) (Tree a b) a b Hole
                 | BNode1 P3 b Hole (Tree a b)
                 | BNode2 P3 b (Tree a b) Hole
    deriving GHC.Generic

instance Generic (Tree a b)

instance Generic (TreeCtx a b)
