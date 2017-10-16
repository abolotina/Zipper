{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, Rank2Types, GADTs,
    UndecidableSuperClasses, TypeApplications #-}
module Base where

import GHC.Exts (Constraint)
import Data.Maybe

import Generics.SOP

import GenericContext

-- =========================================== Base

-- The definitions in this module are common for implementing
-- navigation primitives for the generic zipper.

data Fam (fam :: [*]) (c :: * -> Constraint) = Fam

type family Equal a x :: Bool where
    Equal a a = 'True
    Equal a x = 'False

type family Equals (a :: k) (xs :: [k]) :: [Bool] where
    Equals a (a ': xs) = '[ 'True]
    Equals a (x ': xs) = 'False ': Equals a xs

type IsHole xs = Equals Hole xs

class ProofEq' (p :: Bool) (a :: *) (b :: *) where
    witnessEq :: Proxy p -> Proxy a -> b -> Maybe a

instance ProofEq' 'False a b where
    witnessEq _ _ _ = Nothing
instance ProofEq' 'True a a where
    witnessEq _ _   = Just

type ProofEq a b = ProofEq' (Equal a b) a b

type family All2C (c :: k -> k -> [k] -> Constraint)
                  (a :: k) (b :: k) (xss :: [[k]]) :: Constraint where
    All2C c a b '[]         = ()
    All2C c a b (xs ': xss) = (c a b xs, All2C c a b xss)

type family All2CFam (c :: [k] -> [k] -> Constraint)
                     (fam :: [k]) (xss :: [[k]]) :: Constraint where
    All2CFam c fam '[]         = ()
    All2CFam c fam (xs ': xss) = (c fam xs, All2CFam c fam xss)

type family All2CFam2 (c :: [k] -> k -> k -> [k] -> Constraint)
                      (fam :: [k]) (a :: k) (b :: k)
                      (xss :: [[k]]) :: Constraint where
    All2CFam2 c fam a b '[] = ()
    All2CFam2 c fam a b (xs ': xss)
        = (c fam a b xs, All2CFam2 c fam a b xss)

type family All2CFam2C (c :: [k] -> (k -> Constraint) -> k -> k
                          -> [k] -> Constraint)
                       (fam :: [k]) (u :: k -> Constraint) (a :: k) (b :: k)
                       (xss :: [[k]]) :: Constraint where
    All2CFam2C c fam u a b '[] = ()
    All2CFam2C c fam u a b (xs ': xss)
        = (c fam u a b xs, All2CFam2C c fam u a b xss)

type CtxCode  fam a = ToContext 'F fam (Code a)
type GContext fam a = SOP I (CtxCode fam a)

newtype Context fam a = Ctx {ctx :: GContext fam a}

type family AllProofF (f :: k -> *)
                      (x :: k) (ys :: [k]) :: Constraint where
    AllProofF f x '[]       = ()
    AllProofF f x (y ': ys)
        = (ProofEq' (Equal x y) (f x) (f y), AllProofF f x ys)

class ConsNumInj (n :: ConsNum) (xs :: [k]) where
    consNumInj :: AllProofF f xs yss
               => Proxy n -> Proxy xs -> NP f yss -> f xs

instance ConsNumInj n xs => ConsNumInj ('N n) xs where
    consNumInj _ p (_ :* yss) = consNumInj (Proxy @n) p yss
    consNumInj _ _ Nil        = impossible
instance ConsNumInj 'F xs where
    consNumInj _ _ ((ys :: f ys) :* _)
        = fromMaybe impossible
                    (witnessEq (Proxy @(Equal xs ys))
                               (Proxy @(f xs)) ys)
    consNumInj _ _ Nil = impossible
instance ConsNumInj 'None xs where
    consNumInj _ _ _   = impossible

type family FstRecToHole (fam :: [k]) (xs :: [k]) :: [k] where
    FstRecToHole fam '[]       = '[]
    FstRecToHole fam (a ': xs) = If (In a fam)
                                     (Hole ': xs)
                                     (a    ': FstRecToHole fam xs)

class FromFstRec (xs :: [*]) (ys :: [*]) where
    fromFstRec :: Proxy ys -> NP I xs -> NP I ys

instance FromFstRec (x ': xs) (Hole ': xs) where
    fromFstRec _ (_ :* xs) = I Hole :* xs
instance FromFstRec xs ys => FromFstRec (x ': xs) (x ': ys) where
    fromFstRec _ (x :* xs) = x      :* fromFstRec (Proxy @ys) xs
instance FromFstRec '[] '[] where
    fromFstRec _ _         = Nil

type family All2CN (c :: ConsNum -> [k] -> [k] -> k -> Constraint)
                   (xss :: [[k]]) (fam :: [k]) (a :: k)
                   (n :: ConsNum) :: Constraint where
    All2CN c '[]         fam a n = ()
    All2CN c (xs ': xss) fam a n
        = (c n xs fam a, All2CN c xss fam a ('N n))

type family All2CFN2 (c :: ConsNum -> ([k] -> *) -> [k] -> [k] -> [[k]]
                        -> Constraint)
                     (f :: [k] -> *) (fam :: [k])
                     (xss :: [[k]]) (yss :: [[k]])
                     (n :: ConsNum) :: Constraint where
    All2CFN2 c f fam '[]         yss n = ()
    All2CFN2 c f fam (xs ': xss) yss n
        = (c n f fam xs yss, All2CFN2 c f fam xss yss ('N n))

type AppInj n xs code = (ConsNumInj n xs, SListI code,
                         AllProofF (Injection (NP I) code) xs code)

appCtxInj :: AppInj n xs (CtxCode fam a)
          => Fam fam c -> Proxy a -> Proxy (n :: ConsNum) -> NP I xs
          -> Context fam a
appCtxInj _ _ p np
    = Ctx $ SOP $ unK $ apFn (consNumInj p Proxy injections) np

appInj :: AppInj n xs (Code a)
       => Proxy a -> Proxy (n :: ConsNum) -> NP I xs -> Rep a
appInj _ p np = SOP $ unK $ apFn (consNumInj p Proxy injections) np

-- Internal error function
impossible :: a
impossible =  error "impossible"
