{-# LANGUAGE DeriveGeneric #-}
module TreeExample where

import Generics.SOP
import qualified GHC.Generics as GHC (Generic)

-- An example of a datatype: Tree
data Tree a b = Leaf a
              | TNode (Tree a b) (Tree a b) a b (Tree a b)
              | BNode b (Tree a b) (Tree a b)
    deriving GHC.Generic

data TreeCtx a b = TNode1 (Tree a b) a b (Tree a b)
                 | TNode2 (Tree a b) a b (Tree a b)
                 | TNode3 (Tree a b) (Tree a b) a b
                 | BNode1 b (Tree a b)
                 | BNode2 b (Tree a b)
    deriving GHC.Generic

instance Generic (Tree a b)

instance Generic (TreeCtx a b)
