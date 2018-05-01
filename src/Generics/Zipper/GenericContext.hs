{-# LANGUAGE TypeFamilies, DataKinds, KindSignatures, TypeOperators,
     UndecidableInstances, PolyKinds, ConstraintKinds #-}
-- | Type-level functions of this module implement the machinery of
-- partial differentiation of types. The result of differentiation is
-- the type of the zipper context.
--
-- The basic idea is provided by McBride's /The Derivative of a Regular Type is its Type of One-Hole Contexts/
-- (2001).
--
-- This realization extends that technique for families of mutually
-- recursive types.
--
module Generics.Zipper.GenericContext where

import Generics.SOP (Proxy)

-- ------------------------------------------- Type arithmetic
type family (.++) (xs :: [[*]]) (ys :: [[*]]) :: [[*]] where
    (x ': xs) .++ ys = x ': (xs .++ ys)
    '[]       .++ ys = ys

type family (.*) (x :: *) (ys :: [[*]]) :: [[*]] where
    x .* (ys ': yss) = (x ': ys) ': (x .* yss)
    x .* '[]         = '[]

type family (.**) (xs :: [*]) (ys :: [[*]]) :: [[*]] where
    (x ': xs) .** yss = x .* (xs .** yss)
    '[]       .** yss = yss

infixr 6 .++
infixr 7 .*
infixr 7 .**
-- -------------------------------------------

data ConsNum = F         -- First
             | N ConsNum -- Next
             | None
    deriving Eq

type family InFam (a :: k) (fam :: [k]) :: Bool where
    InFam a (a ': fam) = 'True
    InFam a (x ': fam) = InFam a fam
    InFam a '[]        = 'False

type In a fam = InFam a fam ~ True

type family If (c :: Bool) (t :: k) (e :: k) where
    If 'True  t e = t
    If 'False t e = e

type family ToContext (n :: ConsNum) (fam :: [*]) (code :: [[*]]) :: [[*]] where
    ToContext n fam '[] = '[]
    ToContext n fam (xs ': xss)
        = Proxy n .* DiffProd fam xs .++ ToContext ('N n) fam xss

data Hole = Hole
data End

type family DiffProd (fam :: [*]) (xs :: [*]) :: [[*]] where
    DiffProd fam '[]       = '[]
    DiffProd fam '[x]      = If (InFam x fam) '[ '[Hole]] '[]
    DiffProd fam '[End, x] = If (InFam x fam) '[ '[]]     '[]
    DiffProd fam (x ': xs)
        = Hole .* xs .** DiffProd fam '[End, x] .++ x .* DiffProd fam xs
