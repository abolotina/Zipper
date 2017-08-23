{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables #-}
module TreeZipper where

import GHC.Exts (Constraint)
import Data.Maybe

import Generics.SOP

import TreeExample
import GenericContext

-- =========================================== Tree zipper implementation
type family Equal a x :: Bool where
    Equal a a = 'True
    Equal a x = 'False

class Proof (p :: Bool) (a :: *) (b :: *) where
    witness :: Proxy p -> Proxy a -> b -> Maybe a

instance Proof 'False a b where
    witness _ _ _ = Nothing
instance Proof 'True a a where
    witness _ _   = Just

-- ------------------------------------------- toFirst
{-toFirst :: Tree a b -> Tree a b
toFirst (Leaf _)          = impossible
toFirst (TNode t _ _ _ _) = t
toFirst (BNode _ t _)     = t-}

toFirst :: (Generic a, ToFirst a) => a -> Maybe a
toFirst t = toFirstNS (Proxy :: Proxy a) (unSOP $ from t)

toFirstNS :: All2Proof a xss => Proxy a -> NS (NP I) xss -> Maybe a
toFirstNS p (S ns) = toFirstNS p ns
toFirstNS p (Z np) = toFirstNP p np

type family AllProof (x :: k) (ys :: [k]) :: Constraint where
    AllProof x '[]       = ()
    AllProof x (y ': ys) = (Proof (Equal x y) x y, AllProof x ys)

type family All2Proof (x :: k) (yss :: [[k]]) :: Constraint where
    All2Proof x '[]         = ()
    All2Proof x (ys ': yss) = (AllProof x ys, All2Proof x yss)

type ToFirst a = All2Proof a (Code a)

toFirstNP :: AllProof a xs => Proxy a -> NP I xs -> Maybe a
toFirstNP (p :: Proxy a) (I (x :: b) :* xs)
    = fromMaybe (toFirstNP p xs)
                (case witness (Proxy :: Proxy (Equal a b)) p x of
                     Nothing -> Nothing
                     t       -> Just t)
toFirstNP _ Nil = Nothing

-- ------------------------------------------- toCtxFirst
{-type GTreeCtx a b = SOP I (Code (TreeCtx a b))

toCtxFirst :: Tree a b -> GTreeCtx a b
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = from (TNode1 Proxy Hole m x y r)
toCtxFirst (BNode x _ r)     = from (BNode1 Proxy x Hole r)-}

type CtxCode  a = ToContext 'F a (Code a)
type GContext a = SOP I (CtxCode a)

toCtxFirst :: (Generic a, ToCtxFirst a) => a -> GContext a
toCtxFirst (t :: a) = toCtxFirstNS (Proxy :: Proxy a)
                                   (Proxy :: Proxy 'F) (unSOP $ from t)

type family CtxConsNum (xss :: [[k]]) (n :: ConsNum) :: ConsNum where
    CtxConsNum '[]                       n = 'None
    CtxConsNum ((Proxy n  ': xs) ': xss) n = 'F
    CtxConsNum ((Proxy n' ': xs) ': xss) n = 'N (CtxConsNum xss n)

type family AllProofF (f :: k -> *) (x :: k) (ys :: [k]) :: Constraint where
    AllProofF f x '[]       = ()
    AllProofF f x (y ': ys) = (Proof (Equal x y) (f x) (f y), AllProofF f x ys)

class CtxConsNumInj (n :: ConsNum) (xs :: [k]) where
    ctxConsNumInj :: AllProofF f xs yss
                  => Proxy n -> Proxy xs -> NP f yss -> f xs

instance CtxConsNumInj n xs => CtxConsNumInj ('N n) xs where
    ctxConsNumInj _ p (_ :* yss) = ctxConsNumInj (Proxy :: Proxy n) p yss
    ctxConsNumInj _ _ Nil        = impossible
instance CtxConsNumInj 'F xs where
    ctxConsNumInj _ _ ((ys :: f ys) :* _)
        = fromMaybe impossible
                    (witness (Proxy :: Proxy (Equal xs ys))
                             (Proxy :: Proxy (f xs)) ys)
    ctxConsNumInj _ _ Nil = impossible
instance CtxConsNumInj 'None xs where
    ctxConsNumInj _ _ _   = impossible

type family FstRecToHole (a :: k) (xs :: [k]) :: [k] where
    FstRecToHole a (a ': xs) = Hole ': xs
    FstRecToHole a (x ': xs) = x    ': FstRecToHole a xs
    FstRecToHole a '[]       = '[]

class FromFstRec (xs :: [*]) (ys :: [*]) where
    fromFstRec :: Proxy ys -> NP I xs -> NP I ys

instance FromFstRec xs ys => FromFstRec (x ': xs) (Hole ': ys) where
    fromFstRec _ (_ :* xs) = I Hole :* fromFstRec (Proxy :: Proxy ys) xs
instance FromFstRec xs ys => FromFstRec (x ': xs) (x ': ys) where
    fromFstRec _ (x :* xs) = x      :* fromFstRec (Proxy :: Proxy ys) xs
instance FromFstRec '[] '[] where
    fromFstRec _ _         = Nil

type family AllCtxConsNumInj (a :: k) (n :: ConsNum)
                             (xss :: [[k]]) :: Constraint where
    AllCtxConsNumInj a n '[]         = ()
    AllCtxConsNumInj a n (xs ': xss)
        = (CtxConsNumInj (CtxConsNum (CtxCode a) n)
                         (Proxy n ': FstRecToHole a xs),
           AllCtxConsNumInj a n xss, AllCtxConsNumInj a ('N n) xss)

type family AllFromFstRec (a :: k) (xss :: [[k]]) :: Constraint where
    AllFromFstRec a '[] = ()
    AllFromFstRec a (xs ': xss)
        = (FromFstRec xs (FstRecToHole a xs), AllFromFstRec a xss)

type family AllProofF2Ctx (f :: [k] -> *) (xs :: [[k]]) (ys :: [[k]])
                       (n :: ConsNum) (a :: k) :: Constraint where
    AllProofF2Ctx f '[]       ys n a = ()
    AllProofF2Ctx f (x ': xs) ys n a
        = (AllProofF f (Proxy n ': FstRecToHole a x) ys,
           AllProofF2Ctx f xs ys n a, AllProofF2Ctx f xs ys ('N n) a)

type ToCtxFirst a = (SListI (CtxCode a), AllFromFstRec a (Code a),
                     AllCtxConsNumInj a 'F (Code a),
                     AllProofF2Ctx (Injection (NP I) (CtxCode a))
                                   (Code a) (CtxCode a) 'F a)

toCtxFirstNS :: (SListI (CtxCode a), AllFromFstRec a xss,
                 AllCtxConsNumInj a n xss,
                 AllProofF2Ctx (Injection (NP I) (CtxCode a)) xss
                               (CtxCode a) n a)
             => Proxy a -> Proxy (n :: ConsNum) -> NS (NP I) xss -> GContext a
toCtxFirstNS p (_ :: Proxy n) (S ns)
    = toCtxFirstNS p (Proxy :: Proxy ('N n)) ns
toCtxFirstNS (_ :: Proxy a) (_ :: Proxy n) (Z (np :: NP I xs)) = SOP $ unK $
    apFn (ctxConsNumInj (Proxy :: Proxy (CtxConsNum (CtxCode a) n))
                        Proxy injections)
         (I (Proxy :: Proxy n) :*
          fromFstRec (Proxy :: Proxy (FstRecToHole a xs)) np)

-- -------------------------------------------
type GCtxTreeIB = GContext TreeIB

fillCtx :: GCtxTreeIB -> TreeIB -> TreeIB
fillCtx tc t = case to tc of
    TNode1 _ _ m x y r -> TNode t m x y r
    TNode2 _ l _ x y r -> TNode l t x y r
    TNode3 _ l m x y _ -> TNode l m x y t
    BNode1 _ x _ r     -> BNode x t r
    BNode2 _ x l _     -> BNode x l t

nextCtx :: GCtxTreeIB -> TreeIB -> GCtxTreeIB
nextCtx tc t = case to tc of
    TNode1 _ _ _ x y r -> from (TNode2 Proxy t Hole x y r)
    TNode2 _ l _ x y _ -> from (TNode3 Proxy l t x y Hole)
    TNode3{}         -> impossible
    BNode1 _ x _ _     -> from (BNode2 Proxy x t Hole)
    BNode2{}         -> impossible

nextFromCtx :: GCtxTreeIB -> TreeIB
nextFromCtx tc = case to tc of
    TNode1 _ _ t _ _ _ -> t
    TNode2 _ _ _ _ _ t -> t
    TNode3{}         -> impossible
    BNode1 _ _ _ t     -> t
    BNode2{}         -> impossible

-- ------------------------------------------- Navigation functions
type Loc a     = (a, [GContext a])
type LocTreeIB = Loc TreeIB

type GoDown a = (ToFirst a, ToCtxFirst a)

goDown :: (Generic a, GoDown a) => Loc a -> Maybe (Loc a)
goDown (t, cs) = case toFirst t of
    Just t' -> Just (t', toCtxFirst t : cs)
    _       -> Nothing

goRight :: LocTreeIB -> Maybe LocTreeIB
goRight (_, [])     = Nothing
goRight (t, c : cs) = Just (nextFromCtx c, nextCtx c t : cs)

goUp :: LocTreeIB -> Maybe LocTreeIB
goUp (_, [])     = Nothing
goUp (t, c : cs) = Just (fillCtx c t, cs)

-- Start navigating
enter :: TreeIB -> LocTreeIB
enter hole = (hole, [])

-- End navigating
leave :: LocTreeIB -> TreeIB
leave (hole, []) = hole
leave loc        = leave $ fromJust $ goUp loc

-- Update the current focus
update :: (TreeIB -> TreeIB) -> LocTreeIB -> LocTreeIB
update f (hole, cs) = (f hole, cs)

-- Flipped function composition
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) f g = g . f

-- Internal error function
impossible :: a
impossible =  error "impossible"
