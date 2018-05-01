{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, Rank2Types, GADTs,
    UndecidableSuperClasses, TypeApplications, AllowAmbiguousTypes #-}
-- | Definitions in this module are common for implementing
-- navigation primitives for the generic zipper.
module Generics.Zipper.Base (
    module Generics.Zipper.Base
    -- * Re-exports
  , module Generics.SOP) where

import GHC.Exts (Constraint)
import Data.Maybe

import Generics.SOP

import Generics.Zipper.GenericContext

-- =========================================== Base

type CtxCode  fam a = ToContext 'F fam (Code a)
type GContext fam a = SOP I (CtxCode fam a)

newtype Context fam a = Ctx {ctx :: SOP I (CtxCode fam a)}

type family Equal a x :: Bool where
    Equal a a = 'True
    Equal a x = 'False

type family Equals (a :: k) (xs :: [k]) :: [Bool] where
    Equals a (a ': xs) = '[ 'True]
    Equals a (x ': xs) = 'False ': Equals a xs

type IsHole xs = Equals Hole xs

class ProofEq' (p :: Bool) (a :: *) (b :: *) where
    witnessEq :: b -> Maybe a

instance ProofEq' 'False a b where
    witnessEq _ = Nothing
instance ProofEq' 'True a a where
    witnessEq   = Just

type ProofEq a b = ProofEq' (Equal a b) a b

class ProofEq' (Equal a b) (f a) (f b) => ProofF f a b
instance ProofEq' (Equal a b) (f a) (f b) => ProofF f a b

type family AllNum (c :: k -> ConsNum -> Constraint)
                 (xs :: [k]) (n :: ConsNum) :: Constraint where
    AllNum c '[]       n = ()
    AllNum c (x ': xs) n = (c x n, AllNum c xs ('N n))

class ConsNumInj (n :: ConsNum) (xs :: [*]) where
    consNumInj :: All (ProofF f xs) yss => NP f yss -> f xs

instance ConsNumInj n xs => ConsNumInj ('N n) xs where
    consNumInj (_ :* yss) = consNumInj @n yss
    consNumInj Nil        = impossible
instance ConsNumInj 'F xs where
    consNumInj ((ys :: f ys) :* _)
        = fromMaybe impossible $ witnessEq @(Equal xs ys) ys
    consNumInj Nil = impossible
instance ConsNumInj 'None xs where
    consNumInj _   = impossible

type family FstRecToHole (fam :: [k]) (xs :: [k]) :: [k] where
    FstRecToHole fam '[]       = '[]
    FstRecToHole fam (a ': xs) = If (InFam a fam)
                                     (Hole ': xs)
                                     (a    ': FstRecToHole fam xs)

class FromFstRec (ys :: [*]) (xs :: [*]) where
    fromFstRec :: NP I xs -> NP I ys

instance FromFstRec (Hole ': xs) (x ': xs) where
    fromFstRec (_ :* xs) = I Hole :* xs
instance FromFstRec ys xs => FromFstRec (x ': ys) (x ': xs) where
    fromFstRec (x :* xs) = x      :* fromFstRec xs
instance FromFstRec '[] '[] where
    fromFstRec _         = Nil

type AppInj n xs code = (ConsNumInj n xs, SListI code,
                         All (ProofF (Injection (NP I) code) xs) code)

appCtxInj :: forall n a xs fam . AppInj n xs (CtxCode fam a)
          => NP I xs -> Context fam a
appCtxInj np = Ctx $ SOP $ unK $ apFn (consNumInj @n injections) np

appInj :: forall a n xs . (AppInj n xs (Code a))
       => NP I xs -> Rep a
appInj np = SOP $ unK $ apFn (consNumInj @n injections) np

-- Internal error function
impossible :: a
impossible =  error "impossible"
