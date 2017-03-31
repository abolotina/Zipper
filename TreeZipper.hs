{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances #-}
module TreeZipper where

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

instance Generic (TreeCtx a b) where
{-    type Code (TreeCtx a b) = '[ '[Tree a b, a, b, Tree a b],
                                 '[Tree a b, a, b, Tree a b],
                                 '[Tree a b, Tree a b, a, b],
                                 '[b, Tree a b],
                                 '[b, Tree a b]
                               ]-}
    type Code (TreeCtx a b) = ToContext (Tree a b) (Code (Tree a b))
    from tc     = SOP (fromTreeCtx tc)
    to (SOP tc) = toTreeCtx tc

fromTree :: Tree a b -> NS (NP I) (Code (Tree a b))
fromTree (Leaf x)          = Z (I x :* Nil)
fromTree (TNode l m x y r) = S (Z (I l :* I m :* I x :* I y :* I r :* Nil))
fromTree (BNode x l r)     = S (S (Z (I x :* I l :* I r :* Nil)))

toTree :: NS (NP I) (Code (Tree a b)) -> Tree a b
toTree (Z (I x :* Nil))                                 = Leaf x
toTree (S (Z (I l :* I m :* I x :* I y :* I r :* Nil))) = TNode l m x y r
toTree (S (S (Z (I x :* I l :* I r :* Nil))))           = BNode x l r

-- A Regular instance
{-instance Regular (Tree a b) where
    type PF (Tree a b) = K a
                     :+: I :*: I :*: K a :*: K b :*: I
                     :+: K b :*: I :*: I

    from (Leaf x)          = L (K x)
    from (TNode l m x y r) = R (L (I l :*: I m :*: K x :*: K y :*: I r))
    from (BNode x l r)     = R (R (K x :*: I l :*: I r))

    to (L (K x))                                     = Leaf x
    to (R (L (I l :*: I m :*: K x :*: K y :*: I r))) = TNode l m x y r
    to (R (R (K x :*: I l :*: I r)))                 = BNode x l r-}

-- ------------------------------------------- Tree Context
fromTreeCtx :: TreeCtx a b -> NS (NP I) (Code (TreeCtx a b))
fromTreeCtx (TNode1 m x y r) = Z (I m :* I x :* I y :* I r :* Nil)
fromTreeCtx (TNode2 l x y r) = S (Z (I l :* I x :* I y :* I r :* Nil))
fromTreeCtx (TNode3 l m x y) = S (S (Z (I l :* I m :* I x :* I y :* Nil)))
fromTreeCtx (BNode1 x r)     = S (S (S (Z (I x :* I r :* Nil))))
fromTreeCtx (BNode2 x l)     = S (S (S (S (Z (I x :* I l :* Nil)))))

toTreeCtx :: NS (NP I) (Code (TreeCtx a b)) -> TreeCtx a b
toTreeCtx (Z (I m :* I x :* I y :* I r :* Nil))         = TNode1 m x y r
toTreeCtx (S (Z (I l :* I x :* I y :* I r :* Nil)))     = TNode2 l x y r
toTreeCtx (S (S (Z (I l :* I m :* I x :* I y :* Nil)))) = TNode3 l m x y
toTreeCtx (S (S (S (Z (I x :* I r :* Nil)))))           = BNode1 x r
toTreeCtx (S (S (S (S (Z (I x :* I l :* Nil))))))       = BNode2 x l

-- ------------------------------------------- Tree zipper implementation
type GTreeCtx a b = SOP I (Code (TreeCtx a b))

toCtxFirst :: Tree a b -> GTreeCtx a b
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = SOP (fromTreeCtx (TNode1 m x y r))
toCtxFirst (BNode x _ r)     = SOP (fromTreeCtx (BNode1 x r))

toFirst :: Tree a b -> Tree a b
toFirst (Leaf _)          = impossible
toFirst (TNode t _ _ _ _) = t
toFirst (BNode _ t _)     = t

fillCtx :: GTreeCtx a b -> Tree a b -> Tree a b
fillCtx tc t = case toTreeCtx $ unSOP tc of
    TNode1 m x y r -> TNode t m x y r
    TNode2 l x y r -> TNode l t x y r
    TNode3 l m x y -> TNode l m x y t
    BNode1 x r     -> BNode x t r
    BNode2 x l     -> BNode x l t

nextCtx :: GTreeCtx a b -> Tree a b -> GTreeCtx a b
nextCtx tc t = case toTreeCtx $ unSOP tc of
    TNode1 _ x y r -> SOP (fromTreeCtx (TNode2 t x y r))
    TNode2 l x y _ -> SOP (fromTreeCtx (TNode3 l t x y))
    TNode3{}       -> impossible
    BNode1 x _     -> SOP (fromTreeCtx (BNode2 x t))
    BNode2{}       -> impossible

nextFromCtx :: GTreeCtx a b -> Tree a b
nextFromCtx tc = case toTreeCtx $ unSOP tc of
    TNode1 t _ _ _ -> t
    TNode2 _ _ _ t -> t
    TNode3{}       -> impossible
    BNode1 _ t     -> t
    BNode2{}       -> impossible

-- ------------------------------------------- Navigation functions
data TreeLoc a b = TreeLoc (Tree a b) [GTreeCtx a b]

goDown :: TreeLoc a b -> Maybe (TreeLoc a b)
goDown (TreeLoc (Leaf _) _) = Nothing
goDown (TreeLoc t cs)       = Just (TreeLoc (toFirst t) (toCtxFirst t : cs))

goRight :: TreeLoc a b -> Maybe (TreeLoc a b)
goRight (TreeLoc _ [])       = Nothing
goRight (TreeLoc t (c : cs)) = Just (TreeLoc (nextFromCtx c) (nextCtx c t : cs))

goUp :: TreeLoc a b -> Maybe (TreeLoc a b)
goUp (TreeLoc _ [])       = Nothing
goUp (TreeLoc t (c : cs)) = Just (TreeLoc (fillCtx c t) cs)

-- Start navigating
enter :: Tree a b -> TreeLoc a b
enter hole = TreeLoc hole []

-- End navigating
leave :: TreeLoc a b -> Tree a b
leave (TreeLoc hole []) = hole
leave loc           = leave $ fromJust $ goUp loc

-- Update the current focus
update :: (Tree a b -> Tree a b) -> TreeLoc a b -> TreeLoc a b
update f (TreeLoc hole cs) = TreeLoc (f hole) cs

-- Flipped function composition
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) f g = g . f

-- Internal error function
impossible :: a
impossible =  error "impossible"
