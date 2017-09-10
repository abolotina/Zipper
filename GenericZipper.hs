{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, Rank2Types,
    UndecidableSuperClasses #-}
module GenericZipper where

import GHC.Exts (Constraint)
import Data.Maybe

import Generics.SOP

import TreeExample
import GenericContext

----------------------------------------------------------------------------
--                     Generic zipper implementation
----------------------------------------------------------------------------
-- =========================================== Base

-- The definitions in this section are common for implementing
-- navigation primitives for the generic zipper.

type family Equal a x :: Bool where
    Equal a a = 'True
    Equal a x = 'False

class Proof (p :: Bool) (a :: *) (b :: *) where
    witness :: Proxy p -> Proxy a -> b -> Maybe a

instance Proof 'False a b where
    witness _ _ _ = Nothing
instance Proof 'True a a where
    witness _ _   = Just

type family AllProof (x :: k) (ys :: [k]) :: Constraint where
    AllProof x '[]       = ()
    AllProof x (y ': ys) = (Proof (Equal x y) x y, AllProof x ys)

type family All2C (c :: k -> [k] -> Constraint)
                  (x :: k) (yss :: [[k]]) :: Constraint where
    All2C c x '[]         = ()
    All2C c x (ys ': yss) = (c x ys, All2C c x yss)

appToNP :: All2C c a xss
        => (forall xs. c a xs => Proxy a -> NP I xs -> Maybe a)
        -> Proxy c -> Proxy a -> NS (NP I) xss -> Maybe a
appToNP f c p (S ns) = appToNP f c p ns
appToNP f _ p (Z np) = f p np

-- ===========================================
-- ------------------------------------------- toFirst
{-toFirst :: TreeIB -> TreeIB
toFirst (Leaf _)          = impossible
toFirst (TNode t _ _ _ _) = t
toFirst (BNode _ t _)     = t-}

toFirst :: (Generic a, ToFirst a) => a -> Maybe a
toFirst t = appToNP toFirstNP (Proxy :: Proxy AllProof')
                              (Proxy :: Proxy a) (unSOP $ from t)

class AllProof x ys => AllProof' x ys
instance AllProof x ys => AllProof' x ys

type ToFirst a = All2C AllProof' a (Code a)

toFirstNP :: AllProof a xs => Proxy a -> NP I xs -> Maybe a
toFirstNP (p :: Proxy a) (I (x :: b) :* xs)
    = fromMaybe (toFirstNP p xs)
                (case witness (Proxy :: Proxy (Equal a b)) p x of
                     Nothing -> Nothing
                     t       -> Just t)
toFirstNP _ Nil = Nothing

-- ===========================================
type CtxCode  a = ToContext 'F a (Code a)
type GContext a = SOP I (CtxCode a)

type family AllProofF (f :: k -> *)
                      (x :: k) (ys :: [k]) :: Constraint where
    AllProofF f x '[]       = ()
    AllProofF f x (y ': ys)
        = (Proof (Equal x y) (f x) (f y), AllProofF f x ys)

class ConsNumInj (n :: ConsNum) (xs :: [k]) where
    consNumInj :: AllProofF f xs yss
               => Proxy n -> Proxy xs -> NP f yss -> f xs

instance ConsNumInj n xs => ConsNumInj ('N n) xs where
    consNumInj _ p (_ :* yss) = consNumInj (Proxy :: Proxy n) p yss
    consNumInj _ _ Nil        = impossible
instance ConsNumInj 'F xs where
    consNumInj _ _ ((ys :: f ys) :* _)
        = fromMaybe impossible
                    (witness (Proxy :: Proxy (Equal xs ys))
                             (Proxy :: Proxy (f xs)) ys)
    consNumInj _ _ Nil = impossible
instance ConsNumInj 'None xs where
    consNumInj _ _ _   = impossible

type family FstRecToHole (a :: k) (xs :: [k]) :: [k] where
    FstRecToHole a (a ': xs) = Hole ': xs
    FstRecToHole a (x ': xs) = x    ': FstRecToHole a xs
    FstRecToHole a '[]       = '[]

class FromFstRec (xs :: [*]) (ys :: [*]) where
    fromFstRec :: Proxy ys -> NP I xs -> NP I ys

instance FromFstRec (x ': xs) (Hole ': xs) where
    fromFstRec _ (_ :* xs) = I Hole :* xs
instance FromFstRec xs ys => FromFstRec (x ': xs) (x ': ys) where
    fromFstRec _ (x :* xs) = x      :* fromFstRec (Proxy :: Proxy ys) xs
instance FromFstRec '[] '[] where
    fromFstRec _ _         = Nil

type family All2CN (c :: ConsNum -> [k] -> k -> Constraint)
                   (xss :: [[k]]) (a :: k)
                   (n :: ConsNum) :: Constraint where
    All2CN c '[]         a n = ()
    All2CN c (xs ': xss) a n
        = (c n xs a, All2CN c xss a n, All2CN c xss a ('N n))

type family All2CFN2 (c :: ConsNum -> ([k] -> *) -> [k] -> [[k]] -> k
                        -> Constraint)
                     (f :: [k] -> *) (xss :: [[k]]) (yss :: [[k]]) (a :: k)
                     (n :: ConsNum) :: Constraint where
    All2CFN2 c f '[]         yss a n = ()
    All2CFN2 c f (xs ': xss) yss a n
        = (c n f xs yss a,
           All2CFN2 c f xss yss a n, All2CFN2 c f xss yss a ('N n))

type AppInj n xs code = (ConsNumInj n xs, SListI code,
                         AllProofF (Injection (NP I) code) xs code)

appCtxInj :: AppInj n xs (CtxCode a)
          => Proxy a -> Proxy (n :: ConsNum) -> NP I xs -> GContext a
appCtxInj _ p np = SOP $ unK $ apFn (consNumInj p Proxy injections) np

appInj :: AppInj n xs (Code a)
       => Proxy a -> Proxy (n :: ConsNum) -> NP I xs -> Rep a
appInj _ p np = SOP $ unK $ apFn (consNumInj p Proxy injections) np

-- ===========================================
-- ------------------------------------------- toCtxFirst
{-toCtxFirst :: TreeIB -> GContext TreeIB
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = from (TNode1 Proxy Hole m x y r)
toCtxFirst (BNode x _ r)     = from (BNode1 Proxy x Hole r)-}

toCtxFirst :: (Generic a, ToCtxFirst a) => a -> GContext a
toCtxFirst (t :: a) = toCtxFirstNS (Proxy :: Proxy a)
                                   (Proxy :: Proxy 'F) (unSOP $ from t)

type family CtxConsNum (xss :: [[k]]) (n :: ConsNum) :: ConsNum where
    CtxConsNum '[]                       n = 'None
    CtxConsNum ((Proxy n  ': xs) ': xss) n = 'F
    CtxConsNum ((Proxy n' ': xs) ': xss) n = 'N (CtxConsNum xss n)

class ConsNumInj (CtxConsNum (CtxCode a) n)
                 (Proxy n ': FstRecToHole a xs) => CtxConsNInj n xs a
instance ConsNumInj (CtxConsNum (CtxCode a) n)
                    (Proxy n ': FstRecToHole a xs) => CtxConsNInj n xs a

class AllProofF f (Proxy n ': FstRecToHole a xs) yss
    => CtxAllProofF n f xs yss a
instance AllProofF f (Proxy n ': FstRecToHole a xs) yss
    => CtxAllProofF n f xs yss a

class FromFstRec xs (FstRecToHole a xs) => FromFstRec' a xs
instance FromFstRec xs (FstRecToHole a xs) => FromFstRec' a xs

type ToCtxFirst' a n xss = (SListI (CtxCode a), All2C FromFstRec' a xss,
                            All2CN CtxConsNInj xss a n,
                            All2CFN2 CtxAllProofF
                                     (Injection (NP I) (CtxCode a))
                                     xss (CtxCode a) a n)

type ToCtxFirst a = ToCtxFirst' a 'F (Code a)

toCtxFirstNS :: ToCtxFirst' a n xss
             => Proxy a -> Proxy (n :: ConsNum)
             -> NS (NP I) xss -> GContext a
toCtxFirstNS p (_ :: Proxy n) (S ns)
    = toCtxFirstNS p (Proxy :: Proxy ('N n)) ns
toCtxFirstNS (p :: Proxy a) (_ :: Proxy n) (Z (np :: NP I xs))
    = appCtxInj p (Proxy :: Proxy (CtxConsNum (CtxCode a) n))
                  (I (Proxy :: Proxy n) :*
                   fromFstRec (Proxy :: Proxy (FstRecToHole a xs)) np)

-- ===========================================
type family IsHole (xs :: [k]) :: [Bool] where
    IsHole (Hole ': xs) = '[ 'True]
    IsHole (x    ': xs) = 'False ': IsHole xs

-- ===========================================
-- ------------------------------------------- fillCtx
{-fillCtx :: GContext TreeIB -> TreeIB -> TreeIB
fillCtx tc t = case to tc of
    TNode1 _ _ m x y r -> TNode t m x y r
    TNode2 _ l _ x y r -> TNode l t x y r
    TNode3 _ l m x y _ -> TNode l m x y t
    BNode1 _ x _ r     -> BNode x t r
    BNode2 _ x l _     -> BNode x l t-}

fillCtx :: (Generic a, FillCtx a) => GContext a -> a -> a
fillCtx c t = to $ fillCtxNS (Proxy :: Proxy a) (unSOP c) t

type family HoleToRec (xs :: [k]) (a :: k) :: [k] where
    HoleToRec (Proxy n ': xs) a = HoleToRec xs a
    HoleToRec (Hole    ': xs) a = a ': xs
    HoleToRec (x       ': xs) a = x ': HoleToRec xs a

class FillHole (bs :: [Bool]) (xs :: [*]) (ys :: [*]) (a :: *) where
    fillHole :: Proxy bs -> Proxy ys -> NP I xs -> a -> NP I ys

instance FillHole bs xs ys a
        => FillHole ('False ': bs) (Proxy n ': xs) ys a where
    fillHole _ _ (_ :* xs)
        = fillHole (Proxy :: Proxy bs) (Proxy :: Proxy ys) xs
instance FillHole '[ 'True] (Hole ': ys) (y ': ys) y where
    fillHole _ _ (_ :* xs) t = I t :* xs
instance FillHole bs xs ys a
        => FillHole ('False ': bs) (y ': xs) (y ': ys) a where
    fillHole _ _ (x :* xs) t
        = x :* fillHole (Proxy :: Proxy bs) (Proxy :: Proxy ys) xs t

type family DataConsNum (xs :: [k]) :: ConsNum where
    DataConsNum (Proxy n ': xs) = n

class (FillHole (IsHole xs) xs (HoleToRec xs a) a,
       ConsNumInj (DataConsNum xs) (HoleToRec xs a),
       AllProofF (Injection (NP I) (Code a)) (HoleToRec xs a) (Code a))
    => FillCtx' a xs

instance (FillHole (IsHole xs) xs (HoleToRec xs a) a,
          ConsNumInj (DataConsNum xs) (HoleToRec xs a),
          AllProofF (Injection (NP I) (Code a)) (HoleToRec xs a) (Code a))
    => FillCtx' a xs

type FillCtx a = All2C FillCtx' a (CtxCode a)

fillCtxNS :: (SListI (Code a), All2C FillCtx' a xss)
          => Proxy a -> NS (NP I) xss -> a -> Rep a
fillCtxNS p (S ns) t = fillCtxNS p ns t
fillCtxNS (p :: Proxy a) (Z (np :: NP I xs)) t
    = appInj p (Proxy :: Proxy (DataConsNum xs))
               (fillHole (Proxy :: Proxy (IsHole xs))
                         (Proxy :: Proxy (HoleToRec xs a)) np t)

-- ------------------------------------------- nextCtx
{-nextCtx :: GContext TreeIB -> TreeIB -> GContext TreeIB
nextCtx tc t = case to tc of
    TNode1 _ _ _ x y r -> from (TNode2 Proxy t Hole x y r)
    TNode2 _ l _ x y _ -> from (TNode3 Proxy l t x y Hole)
    TNode3{}           -> impossible
    BNode1 _ x _ _     -> from (BNode2 Proxy x t Hole)
    BNode2{}           -> impossible-}

nextCtx :: (Generic a, NextCtx a) => GContext a -> a -> GContext a
nextCtx c = nextCtxNS (Proxy :: Proxy a) (Proxy :: Proxy 'F) (unSOP c)

type family ToNextHole (xs :: [k]) (a :: k) :: [k] where
    ToNextHole (Proxy n ': xs) a = Proxy n ': ToNextHole xs a
    ToNextHole (Hole    ': xs) a = a       ': FstRecToHole a xs
    ToNextHole (x       ': xs) a = x       ': ToNextHole xs a

class NextHole (bs :: [Bool]) (xs :: [*]) (ys :: [*]) (a :: *) where
    nextHole :: Proxy bs -> Proxy ys -> NP I xs -> a -> NP I ys

instance FromFstRec xs ys
        => NextHole '[ 'True] (Hole ': xs) (y ': ys) y where
    nextHole _ _ (_ :* xs) t = I t :* fromFstRec (Proxy :: Proxy ys) xs
instance NextHole bs xs ys a
        => NextHole ('False ': bs) (y ': xs) (y ': ys) a where
    nextHole _ _ (x :* xs) t
        = x :* nextHole (Proxy :: Proxy bs) (Proxy :: Proxy ys) xs t

class ConsNumInj n (ToNextHole xs a) => NextCtxConsNInj n xs a
instance ConsNumInj n (ToNextHole xs a) => NextCtxConsNInj n xs a

class (NextHole (IsHole xs) xs (ToNextHole xs a) a,
       AllProofF (Injection (NP I) (CtxCode a))
                 (ToNextHole xs a) (CtxCode a))
    => NextCtx'' a xs

instance (NextHole (IsHole xs) xs (ToNextHole xs a) a,
          AllProofF (Injection (NP I) (CtxCode a))
                    (ToNextHole xs a) (CtxCode a))
    => NextCtx'' a xs

type NextCtx' a n xss = (SListI (CtxCode a), All2C NextCtx'' a xss,
                         All2CN NextCtxConsNInj xss a n)

type NextCtx a = NextCtx' a 'F (CtxCode a)

nextCtxNS :: NextCtx' a n xss
          => Proxy a -> Proxy (n :: ConsNum)
          -> NS (NP I) xss -> a -> GContext a
nextCtxNS p (_ :: Proxy n) (S ns) t
    = nextCtxNS p (Proxy :: Proxy ('N n)) ns t
nextCtxNS (p :: Proxy a) (_ :: Proxy n) (Z (np :: NP I xs)) t
    = appCtxInj p (Proxy :: Proxy ('N n))
                  (nextHole (Proxy :: Proxy (IsHole xs))
                            (Proxy :: Proxy (ToNextHole xs a)) np t)

-- ------------------------------------------- nextFromCtx
{-nextFromCtx :: GContext TreeIB -> TreeIB
nextFromCtx tc = case to tc of
    TNode1 _ _ t _ _ _ -> t
    TNode2 _ _ _ _ _ t -> t
    TNode3{}           -> impossible
    BNode1 _ _ _ t     -> t
    BNode2{}           -> impossible-}

nextFromCtx :: (Generic a, NextFromCtx a) => GContext a -> Maybe a
nextFromCtx c = appToNP nextFromCtxNP (Proxy :: Proxy NextFromCtx')
                                      (Proxy :: Proxy a) (unSOP c)

type family AfterHole (xs :: [k]) :: [k] where
    AfterHole (Hole ': xs) = xs
    AfterHole (x    ': xs) = AfterHole xs

class FindHole (bs :: [Bool]) (xs :: [*]) (ys :: [*]) where
    afterHole :: Proxy bs -> Proxy ys -> NP I xs -> NP I ys

instance FindHole bs xs ys => FindHole ('False ': bs) (x ': xs) ys where
    afterHole _ p (_ :* xs) = afterHole (Proxy :: Proxy bs) p xs
instance FindHole '[ 'True] (Hole ': ys) ys where
    afterHole _ _ (_ :* xs) = xs

class (AllProof a (AfterHole xs), FindHole (IsHole xs) xs (AfterHole xs))
    => NextFromCtx' a xs
instance (AllProof a (AfterHole xs), FindHole (IsHole xs) xs (AfterHole xs))
    => NextFromCtx' a xs

type NextFromCtx a = All2C NextFromCtx' a (CtxCode a)

nextFromCtxNP :: NextFromCtx' a xs => Proxy a -> NP I xs -> Maybe a
nextFromCtxNP p (ys :: NP I xs)
    = toFirstNP p $ afterHole (Proxy :: Proxy (IsHole xs))
                              (Proxy :: Proxy (AfterHole xs)) ys

-- ------------------------------------------- Navigation functions
type Loc a     = (a, [GContext a])

type GoDown  a = (ToFirst a, ToCtxFirst a)
type GoRight a = (NextCtx a, NextFromCtx a)
type GoUp    a = FillCtx a

goDown :: (Generic a, GoDown a) => Loc a -> Maybe (Loc a)
goDown (t, cs) = case toFirst t of
    Just t' -> Just (t', toCtxFirst t : cs)
    _       -> Nothing

goRight :: (Generic a, GoRight a) => Loc a -> Maybe (Loc a)
goRight (_, [])     = Nothing
goRight (t, c : cs) = case nextFromCtx c of
    Just t' -> Just (t', nextCtx c t : cs)
    _       -> Nothing

goUp :: (Generic a, GoUp a) => Loc a -> Maybe (Loc a)
goUp (_, [])     = Nothing
goUp (t, c : cs) = Just (fillCtx c t, cs)

-- Start navigating
enter :: Generic a => a -> Loc a
enter hole = (hole, [])

-- End navigating
leave :: (Generic a, GoUp a) => Loc a -> a
leave (hole, []) = hole
leave loc        = leave $ fromJust $ goUp loc

-- Update the current focus
update :: Generic a => (a -> a) -> Loc a -> Loc a
update f (hole, cs) = (f hole, cs)

-- Flipped function composition
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) f g = g . f

-- Internal error function
impossible :: a
impossible =  error "impossible"
