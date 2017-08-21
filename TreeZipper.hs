{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, FunctionalDependencies #-}
module TreeZipper where

import GHC.Exts (Constraint)
import Data.Maybe

import Generics.SOP

import TreeExample
import GenericContext

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

type family Equal a x :: Bool where
    Equal a a = 'True
    Equal a x = 'False

class Proof (p :: Bool) (a :: *) (b :: *) where
    witness :: Proxy p -> Proxy a -> b -> Maybe a

instance Proof 'False a b where
    witness _ _ _ = Nothing
instance Proof 'True a a where
    witness _ _   = Just

type family AllProof (a :: k) (xs :: [k]) :: Constraint where
    AllProof a '[]       = ()
    AllProof a (x ': xs) = (Proof (Equal a x) a x, AllProof a xs)

type family All2Proof (a :: k) (xss :: [[k]]) :: Constraint where
    All2Proof a '[]         = ()
    All2Proof a (xs ': xss) = (AllProof a xs, All2Proof a xss)

toFirstNP :: AllProof a xs => Proxy a -> NP I xs -> a
toFirstNP (p :: Proxy a) (I (x :: b) :* xs)
    = fromMaybe (toFirstNP p xs)
                (witness (Proxy :: Proxy (Equal a b)) p x)
toFirstNP _ Nil = impossible

-- ------------------------------------------- toCtxFirst
type GTreeCtx a b = SOP I (Code (TreeCtx a b))

toCtxFirst :: Tree a b -> GTreeCtx a b
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = from (TNode1 m x y r)
toCtxFirst (BNode x _ r)     = from (BNode1 x r)

type CtxCode  a = ToContext 'F a (Code a)
type GContext a = SOP I (CtxCode a)

toCtxFirst' :: (Generic a, SListI (CtxCode a), AllFromFstRec a (Code a),
                AllCtxConsNumInj a 'F (Code a) (CtxCode a))
            => a -> GContext a
toCtxFirst' (t :: a) = toCtxFirstNS (Proxy :: Proxy a)
                                    (Proxy :: Proxy 'F) (unSOP $ from t)

type family CtxConsNum (xss :: [[k]]) (n :: ConsNum) :: ConsNum where
    CtxConsNum ((Proxy n  ': xs) ': xss) n = 'F
    CtxConsNum ((Proxy n' ': xs) ': xss) n = 'N (CtxConsNum xss n)

class CtxConsNumInj (n :: ConsNum) (yss :: [[k]]) (xs :: [k])
                    | n yss -> xs where
    ctxConsNumInj :: Proxy n -> NP (Injection f xss) yss
                  -> (Injection f xss) xs

instance CtxConsNumInj n yss xs => CtxConsNumInj ('N n) (ys ': yss) xs where
    ctxConsNumInj _ (_ :* yss) = ctxConsNumInj (Proxy :: Proxy n) yss
instance CtxConsNumInj 'F (xs ': yss) xs where
    ctxConsNumInj _ (ys :* _)  = ys

type family FstRecToHole (a :: k) (xs :: [k]) :: [k] where
    FstRecToHole a (a ': xs) = Hole ': xs
    FstRecToHole a (x ': xs) = x    ': FstRecToHole a xs

class FromFstRec (xs :: [*]) (ys :: [*]) where
    fromFstRec :: Proxy ys -> NP I xs -> NP I ys

instance FromFstRec xs ys => FromFstRec (x ': xs) (Hole ': ys) where
    fromFstRec _ (_ :* xs) = I Hole :* fromFstRec (Proxy :: Proxy ys) xs
instance FromFstRec xs ys => FromFstRec (x ': xs) (x ': ys) where
    fromFstRec _ (x :* xs) = x      :* fromFstRec (Proxy :: Proxy ys) xs
instance FromFstRec '[] '[] where
    fromFstRec _ _         = Nil

type family AllCtxConsNumInj (a :: k) (n :: ConsNum)
                             (xss :: [[k]]) (yss :: [[k]]) :: Constraint where
    AllCtxConsNumInj a n '[]         yss = ()
    AllCtxConsNumInj a n (xs ': xss) yss
        = (CtxConsNumInj (CtxConsNum (Code a) n) yss
                         (Proxy n ': FstRecToHole a xs),
           AllCtxConsNumInj a n xss yss, AllCtxConsNumInj a ('N n) xss yss)

type family AllFromFstRec (a :: k) (xss :: [[k]]) :: Constraint where
    AllFromFstRec a '[] = ()
    AllFromFstRec a (xs ': xss)
        = (FromFstRec xs (FstRecToHole a xs), AllFromFstRec a xss)

toCtxFirstNS :: (SListI (CtxCode a), AllFromFstRec a xss,
                 AllCtxConsNumInj a n xss (CtxCode a))
             => Proxy a -> Proxy (n :: ConsNum) -> NS (NP I) xss -> GContext a
toCtxFirstNS p (_ :: Proxy n) (S ns)
    = toCtxFirstNS p (Proxy :: Proxy ('N n)) ns
toCtxFirstNS (_ :: Proxy a) (_ :: Proxy n) (Z (np :: NP I xs)) = SOP $ unK $
    apFn (ctxConsNumInj (Proxy :: Proxy (CtxConsNum (Code a) n)) injections)
         (I (Proxy :: Proxy n) :*
          fromFstRec (Proxy :: Proxy (FstRecToHole a xs)) np)

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
