{-# LANGUAGE TypeFamilies, DataKinds, KindSignatures, TypeOperators,
     UndecidableInstances #-}
module GenericContext where

import Generics.SOP (Proxy)

-- ------------------------------------------- Type arithmetic
type family (.++) (xs :: [[*]]) (ys :: [[*]]) :: [[*]]

type instance (x ': xs) .++ ys = x ': (xs .++ ys)
type instance '[]       .++ ys = ys

type family (.*) (x :: *) (ys :: [[*]]) :: [[*]]

type instance x .* (ys ': yss) = (x ': ys) ': (x .* yss)
type instance x .* '[]         = '[]

type family (.**) (xs :: [*]) (ys :: [[*]]) :: [[*]]

type instance (x ': xs) .** yss = x .* (xs .** yss)
type instance '[]       .** yss = yss

infixr 6 .++
infixr 7 .*
infixr 7 .**
-- -------------------------------------------

data ConsNum = F         -- First
             | N ConsNum -- Next
    deriving Eq

type family ToContext (n :: ConsNum) (a :: *) (code :: [[*]]) :: [[*]]

type instance ToContext n a (xs ': xss)
    = Proxy n .* DiffProd a xs .++ ToContext ('N n) a xss
type instance ToContext n a '[] = '[]

data Hole = Hole
data End

type family DiffProd (a :: *) (xs :: [*]) :: [[*]] where
    DiffProd a '[]       = '[]
    DiffProd a '[a]      = '[ '[Hole]]
    DiffProd a '[x]      = '[]
    DiffProd a '[End, a] = '[ '[]]
    DiffProd a '[End, x] = '[]
    DiffProd a (x ': xs)
        = Hole .* xs .** DiffProd a '[End, x] .++ x .* DiffProd a xs
