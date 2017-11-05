{-# LANGUAGE DataKinds, KindSignatures, PolyKinds,
    TypeOperators, TypeFamilies, FlexibleInstances, ConstraintKinds,
    FlexibleContexts, MultiParamTypeClasses, UndecidableInstances,
    TypeApplications, ScopedTypeVariables, UndecidableSuperClasses #-}

module Generics.GFunctor where

import GHC.Exts (Constraint)

import Generics.SOP

import Generics.Zipper.GenericContext
import Generics.Zipper.Base

-------------------------------------------------
--                                Generic Functor
-------------------------------------------------

gfmap :: GFunctor f a b => (a -> b) -> f a -> f b
gfmap f (t :: f a)
    = to $ gfmapNS (Proxy @f) (Proxy @'F) f $ unSOP $ from t

type family FEq (f :: * -> *)
                (a :: *) (x :: *) :: Bool where
    FEq f a (f a) = 'True
    FEq f a a     = 'True
    FEq f a x     = 'False

type family GFMap (f :: * -> *)
                  (a :: *) (b :: *) (x :: *) where
    GFMap f a b (f a) = f b
    GFMap f a b a     = b
    GFMap f a b x     = x

type family FEqList (f :: * -> *)
                    (a :: *) (xs :: [*]) :: [Bool] where
    FEqList f a (x   ': xs) = FEq f a x ': FEqList f a xs
    FEqList f a '[]         = '[]

type family GFMapList (f :: * -> *)
                  (a :: *) (b :: *) (xs :: [*]) :: [*] where
    GFMapList f a b (x   ': xs) = GFMap f a b x ': GFMapList f a b xs
    GFMapList f a b '[]         = '[]

class GFunctor' bs a b xs ys where
    gfmap' :: Proxy bs -> Proxy ys
           -> (a -> b) -> NP I xs -> NP I ys

instance (GFunctor f a b, GFunctor' bs a b xs ys)
        => GFunctor' ('True ': bs) a b (f a ': xs) (f b ': ys) where
    gfmap' _ _ f (I x :* xs)
        = I (gfmap f x) :* gfmap' (Proxy @bs) (Proxy @ys) f xs
instance GFunctor' bs a b xs ys
        => GFunctor' ('True ': bs) a b (a ': xs) (b ': ys) where
    gfmap' _ _ f (I x :* xs)
        = I (f x) :* gfmap' (Proxy @bs) (Proxy @ys) f xs
instance GFunctor' bs a b xs ys
        => GFunctor' ('False ': bs) a b (x ': xs) (x ': ys) where
    gfmap' _ _ f (x :* xs)
        = x :* gfmap' (Proxy @bs) (Proxy @ys) f xs
instance GFunctor' '[] a b '[] '[] where
    gfmap' _ _ _ _ = Nil

class GFunctor' (FEqList f a xs) a b xs (GFMapList f a b xs)
    => GFunctorMap f a b xs
instance GFunctor' (FEqList f a xs) a b xs (GFMapList f a b xs)
    => GFunctorMap f a b xs

class ConsNumInj n (GFMapList f a b xs) => ConsNumInj' f a b n xs
instance ConsNumInj n (GFMapList f a b xs) => ConsNumInj' f a b n xs

type family AllCN (c :: ConsNum -> k -> Constraint)
                  (xs :: [k]) (n :: ConsNum) :: Constraint where
    AllCN c '[]       n = ()
    AllCN c (x ': xs) n = (c n x, AllCN c xs ('N n))

type AllProofInj f a b xs = AllProofF (Injection (NP I) (Code (f b)))
                                      (GFMapList f a b xs) (Code (f b))

class AllProofInj f a b xs => ProofInj f a b xs
instance AllProofInj f a b xs => ProofInj f a b xs

type GFunctor'' f a b xss n
    = (All (GFunctorMap f a b) xss, All (ProofInj f a b) xss,
       AllCN (ConsNumInj' f a b) xss n, SListI (Code (f b)))

type GFunctor f a b
    = (Generic (f a), Generic (f b), GFunctor'' f a b (Code (f a)) 'F)

gfmapNS :: GFunctor'' f a b xss n
        => Proxy f -> Proxy (n :: ConsNum)
        -> (a -> b) -> NS (NP I) xss -> Rep (f b)
gfmapNS pf (_ :: Proxy n) g (S ns) = gfmapNS pf (Proxy @('N n)) g ns
gfmapNS (pf :: Proxy f) (_ :: Proxy n) (g :: a -> b) (Z np)
    = appInj (Proxy @(f b)) (Proxy @n) $ gfmapNP pf g np

gfmapNP :: GFunctorMap f a b xs
        => Proxy f -> (a -> b) -> NP I xs -> NP I (GFMapList f a b xs)
gfmapNP (pf :: Proxy f) (g :: a -> b) (ys :: NP I xs)
    = gfmap' (Proxy @(FEqList f a xs)) (Proxy @(GFMapList f a b xs)) g ys
