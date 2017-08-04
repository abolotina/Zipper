{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances #-}
module TreeZipper2 where

import Data.Maybe

import Generics.SOP
import GenericContext

-- An example of a datatype: Tree
data Tree a b = Leaf a
              | TNode (Tree a b) (Tree a b) a b (Tree a b)
              | BNode b (Tree a b) (Tree a b)

data TreeCtx a b = TNode1 (Tree a b) a b (Tree a b)
                 | TNode2 (Tree a b) a b (Tree a b)
                 | TNode3 (Tree a b) (Tree a b) a b
                 | BNode1 b (Tree a b)
                 | BNode2 b (Tree a b)

instance Generic (Tree a b) where
    type Code (Tree a b) = '[ '[a],
                              '[Tree a b, Tree a b, a, b, Tree a b],
                              '[b, Tree a b, Tree a b]
                            ]
    from t     = SOP (fromTree t)
    to (SOP t) = toTree t

type TreeIB    = Tree Int Bool
type TreeCtxIB = TreeCtx Int Bool

instance Generic TreeCtxIB where
{-    type Code (TreeCtxIB) = '[ '[TreeIB, Int, Bool, TreeIB],
                                 '[TreeIB, Int, Bool, TreeIB],
                                 '[TreeIB, TreeIB, Int, Bool],
                                 '[Bool, TreeIB],
                                 '[Bool, TreeIB]
                               ]-}
    type Code TreeCtxIB = ToContext TreeIB (Code TreeIB)
    from tc     = SOP (fromTreeCtx tc)
    to (SOP tc) = toTreeCtx tc

type RepTreeContext = SOP I (ToContext TreeIB (Code TreeIB))

fromTree :: Tree a b -> NS (NP I) (Code (Tree a b))
fromTree (Leaf x)          = Z (I x :* Nil)
fromTree (TNode l m x y r) = S (Z (I l :* I m :* I x :* I y :* I r :* Nil))
fromTree (BNode x l r)     = S (S (Z (I x :* I l :* I r :* Nil)))

toTree :: NS (NP I) (Code (Tree a b)) -> Tree a b
toTree (Z (I x :* Nil))                                 = Leaf x
toTree (S (Z (I l :* I m :* I x :* I y :* I r :* Nil))) = TNode l m x y r
toTree (S (S (Z (I x :* I l :* I r :* Nil))))           = BNode x l r

-- ------------------------------------------- Tree Context
fromTreeCtx :: TreeCtxIB -> NS (NP I) (Code TreeCtxIB)
fromTreeCtx (TNode1 m x y r) = Z (I m :* I x :* I y :* I r :* Nil)
fromTreeCtx (TNode2 l x y r) = S (Z (I l :* I x :* I y :* I r :* Nil))
fromTreeCtx (TNode3 l m x y) = S (S (Z (I l :* I m :* I x :* I y :* Nil)))
fromTreeCtx (BNode1 x r)     = S (S (S (Z (I x :* I r :* Nil))))
fromTreeCtx (BNode2 x l)     = S (S (S (S (Z (I x :* I l :* Nil)))))

toTreeCtx :: NS (NP I) (Code TreeCtxIB) -> TreeCtxIB
toTreeCtx (Z (I m :* I x :* I y :* I r :* Nil))         = TNode1 m x y r
toTreeCtx (S (Z (I l :* I x :* I y :* I r :* Nil)))     = TNode2 l x y r
toTreeCtx (S (S (Z (I l :* I m :* I x :* I y :* Nil)))) = TNode3 l m x y
toTreeCtx (S (S (S (Z (I x :* I r :* Nil)))))           = BNode1 x r
toTreeCtx (S (S (S (S (Z (I x :* I l :* Nil))))))       = BNode2 x l

-- ------------------------------------------- Tree zipper implementation
type GTreeCtx = SOP I (Code TreeCtxIB)

toCtxFirst :: TreeIB -> GTreeCtx
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = SOP (fromTreeCtx (TNode1 m x y r))
toCtxFirst (BNode x _ r)     = SOP (fromTreeCtx (BNode1 x r))

toFirst :: TreeIB -> TreeIB
toFirst (Leaf _)          = impossible
toFirst (TNode t _ _ _ _) = t
toFirst (BNode _ t _)     = t

fillCtx :: GTreeCtx -> TreeIB -> TreeIB
fillCtx tc t = case toTreeCtx $ unSOP tc of
    TNode1 m x y r -> TNode t m x y r
    TNode2 l x y r -> TNode l t x y r
    TNode3 l m x y -> TNode l m x y t
    BNode1 x r     -> BNode x t r
    BNode2 x l     -> BNode x l t

nextCtx :: GTreeCtx -> TreeIB -> GTreeCtx
nextCtx tc t = case toTreeCtx $ unSOP tc of
    TNode1 _ x y r -> SOP (fromTreeCtx (TNode2 t x y r))
    TNode2 l x y _ -> SOP (fromTreeCtx (TNode3 l t x y))
    TNode3{}       -> impossible
    BNode1 x _     -> SOP (fromTreeCtx (BNode2 x t))
    BNode2{}       -> impossible

nextFromCtx :: GTreeCtx -> TreeIB
nextFromCtx tc = case toTreeCtx $ unSOP tc of
    TNode1 t _ _ _ -> t
    TNode2 _ _ _ t -> t
    TNode3{}       -> impossible
    BNode1 _ t     -> t
    BNode2{}       -> impossible

-- ------------------------------------------- Navigation functions
data TreeLoc = TreeLoc TreeIB [GTreeCtx]

goDown :: TreeLoc -> Maybe TreeLoc
goDown (TreeLoc (Leaf _) _) = Nothing
goDown (TreeLoc t cs)       = Just (TreeLoc (toFirst t) (toCtxFirst t : cs))

goRight :: TreeLoc -> Maybe TreeLoc
goRight (TreeLoc _ [])       = Nothing
goRight (TreeLoc t (c : cs)) = Just (TreeLoc (nextFromCtx c) (nextCtx c t : cs))

goUp :: TreeLoc -> Maybe TreeLoc
goUp (TreeLoc _ [])       = Nothing
goUp (TreeLoc t (c : cs)) = Just (TreeLoc (fillCtx c t) cs)

-- Start navigating
enter :: TreeIB -> TreeLoc
enter hole = TreeLoc hole []

-- End navigating
leave :: TreeLoc -> TreeIB
leave (TreeLoc hole []) = hole
leave loc           = leave $ fromJust $ goUp loc

-- Update the current focus
update :: (TreeIB -> TreeIB) -> TreeLoc -> TreeLoc
update f (TreeLoc hole cs) = TreeLoc (f hole) cs

-- Flipped function composition
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) f g = g . f

-- Internal error function
impossible :: a
impossible =  error "impossible"
