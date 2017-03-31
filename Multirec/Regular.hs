{-# LANGUAGE TypeOperators, TypeFamilies, StandaloneDeriving, FlexibleContexts #-}
module Regular where

-- The class for a fixed-point representation of regular datatypes
class Regular a where
    -- Pattern functor
    type PF a :: * -> *
    from      :: a      -> PF a a
    to        :: PF a a -> a

-- Generic representation types
data K a       r = K a
data I         r = I r
data U         r = Unit
data (f :+: g) r = L (f r) | R (g r)
data (f :*: g) r = f r :*: g r

infixr 6 :+:
infixr 7 :*:

-- Show instances
instance Show a => Show (K a r) where
    show (K x) = show x
instance Show r => Show (I r) where
    show (I x) = show x
instance Show (U r) where
    show Unit  = show ()
deriving instance (Show (f r), Show (g r)) => Show ((f :+: g) r)
deriving instance (Show (f r), Show (g r)) => Show ((f :*: g) r)
