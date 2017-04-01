{-# LANGUAGE TypeFamilies, DataKinds, KindSignatures, TypeOperators,
     UndecidableInstances #-}
module GenericContext where

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
-- -------------------------------------------

type family ToContext (a :: *) (code :: [[*]]) :: [[*]]

type instance ToContext a (xs ': xss) = DiffProd a xs .++ ToContext a xss
type instance ToContext a '[]         = '[]

type family DiffProd (a :: *) (xs :: [*]) :: [[*]] where
    DiffProd a '[]       = '[]
    DiffProd a '[a]      = '[ '[]]
    DiffProd a '[x]      = '[]
    DiffProd a (x ': xs) = (xs .** DiffProd a '[x]) .++ (x .* DiffProd a xs)
