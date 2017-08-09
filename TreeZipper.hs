{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, DeriveGeneric #-}
module TreeZipper where

import GHC.Exts (Constraint)
import Data.Maybe

import GenericContext
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

-- =========================================== Tree zipper implementation
-- ------------------------------------------- toFirst
{-toFirst :: Tree a b -> Tree a b
toFirst (Leaf _)          = impossible
toFirst (TNode t _ _ _ _) = t
toFirst (BNode _ t _)     = t-}

toFirst :: (Generic a, All2Proof a (Code a)) => a -> a
toFirst t = toFirstNS (Proxy :: Proxy a) (unSOP $ from t)

toFirstNS :: All2Proof a xss => Proxy a -> NS (NP I) xss -> a
toFirstNS p (S ns) = toFirstNS p ns
toFirstNS p (Z np) = toFirstNP p np

type family Check a b :: Bool where
    Check a a = 'True
    Check a x = 'False

class Proof (p :: Bool) (a :: *) (b :: *) where
    witness :: Proxy p -> Proxy a -> Proxy b -> b -> Maybe a

instance Proof 'False a b where
    witness _ _ _ _ = Nothing
instance Proof 'True a a where
    witness _ _ _   = Just

type family AllProof (a :: k) (xs :: [k]) :: Constraint where
    AllProof a '[]       = ()
    AllProof a (x ': xs) = (Proof (Check a x) a x, AllProof a xs)

type family All2Proof (a :: k) (xss :: [[k]]) :: Constraint where
    All2Proof a '[]         = ()
    All2Proof a (xs ': xss) = (AllProof a xs, All2Proof a xss)

toFirstNP :: AllProof a xs => Proxy a -> NP I xs -> a
toFirstNP (p :: Proxy a) (I (x :: b) :* xs)
    = fromMaybe (toFirstNP p xs)
                (witness (Proxy :: Proxy (Check a b)) p Proxy x)
toFirstNP _ Nil = impossible

-- ------------------------------------------- toCtxFirst
type GTreeCtx a b = SOP I (Code (TreeCtx a b))

toCtxFirst :: Tree a b -> GTreeCtx a b
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = from (TNode1 m x y r)
toCtxFirst (BNode x _ r)     = from (BNode1 x r)

class Boolean (b :: Bool) where
    bool :: Proxy b -> Bool
instance Boolean 'True where
    bool _ = True
instance Boolean 'False where
    bool _ = False

type family AllBool (n' :: ConsNum) (xss :: [[k]]) :: Constraint where
    AllBool n' '[] = ()
    AllBool n' ((n ': xs) ': xss)
        = (Boolean (Check n (Proxy n')), AllBool n' xss)

class ContextConsNum (xss :: [[*]]) (n :: ConsNum) where
    ctxConsNum :: AllBool n xss => ConsNum -> Proxy xss -> Proxy n -> ConsNum

instance ContextConsNum xss n' => ContextConsNum ((n ': xs) ': xss) n' where
    ctxConsNum cn _ pn = if bool (Proxy :: Proxy (Check n (Proxy n')))
                             then cn
                             else ctxConsNum (N cn) (Proxy :: Proxy xss) pn

type GContext a = SOP I (ToContext 'F a (Code a))

{-consNumType :: Proxy (n :: ConsNum) -> NS (NP I) xss -> Proxy ('N n)
consNumType (_ :: Proxy n) (S ns) = consNumType (Proxy :: Proxy ('N n)) ns
consNumType cn             (Z _)  = cn-}

{-toCtxFirst' :: Generic a => a -> GContext a
toCtxFirst' t = toCtxFirstNS (Proxy :: Proxy a) (unSOP $ from t)

toCtxFirstNS :: Proxy a -> NS (NP I) xss -> GContext a
toCtxFirstNS-}

-- -------------------------------------------
fillCtx :: GTreeCtx a b -> Tree a b -> Tree a b
fillCtx tc t = case to tc of
    TNode1 m x y r -> TNode t m x y r
    TNode2 l x y r -> TNode l t x y r
    TNode3 l m x y -> TNode l m x y t
    BNode1 x r     -> BNode x t r
    BNode2 x l     -> BNode x l t

nextCtx :: GTreeCtx a b -> Tree a b -> GTreeCtx a b
nextCtx tc t = case to tc of
    TNode1 _ x y r -> from (TNode2 t x y r)
    TNode2 l x y _ -> from (TNode3 l t x y)
    TNode3{}       -> impossible
    BNode1 x _     -> from (BNode2 x t)
    BNode2{}       -> impossible

nextFromCtx :: GTreeCtx a b -> Tree a b
nextFromCtx tc = case to tc of
    TNode1 t _ _ _ -> t
    TNode2 _ _ _ t -> t
    TNode3{}       -> impossible
    BNode1 _ t     -> t
    BNode2{}       -> impossible

-- ------------------------------------------- Navigation functions
type TreeLoc a b = (Tree a b, [GTreeCtx a b])

goDown :: (Generic (Tree a b), All2Proof (Tree a b) (Code (Tree a b)))
       => TreeLoc a b -> Maybe (TreeLoc a b)
goDown (Leaf _, _) = Nothing
goDown (t, cs)     = Just (toFirst t, toCtxFirst t : cs)

goRight :: TreeLoc a b -> Maybe (TreeLoc a b)
goRight (_, [])     = Nothing
goRight (t, c : cs) = Just (nextFromCtx c, nextCtx c t : cs)

goUp :: TreeLoc a b -> Maybe (TreeLoc a b)
goUp (_, [])     = Nothing
goUp (t, c : cs) = Just (fillCtx c t, cs)

-- Start navigating
enter :: Tree a b -> TreeLoc a b
enter hole = (hole, [])

-- End navigating
leave :: TreeLoc a b -> Tree a b
leave (hole, []) = hole
leave loc        = leave $ fromJust $ goUp loc

-- Update the current focus
update :: (Tree a b -> Tree a b) -> TreeLoc a b -> TreeLoc a b
update f (hole, cs) = (f hole, cs)

-- Flipped function composition
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) f g = g . f

-- Internal error function
impossible :: a
impossible =  error "impossible"
