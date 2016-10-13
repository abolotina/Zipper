{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleContexts, GADTs,
    TypeOperators, FlexibleInstances, UndecidableInstances #-}
module Zipper where

import Data.Maybe
import Control.Monad
import Prelude hiding (last)

import Regular

-- Location
data Loc a where
    Loc :: (Regular a, Zipper (PF a) a) => a -> Context a -> Loc a

-- Context stack
data Context a = CNil | Context (Ctxt (PF a) a) (Context a)

-- Context frame
data family Ctxt (f :: * -> *) a

-- Start navigating
enter :: (Regular a, Zipper (PF a) a) => a -> Loc a
enter hole = Loc hole CNil

-- End navigating
leave :: Loc a -> a
leave (Loc hole CNil) = hole
leave loc             = leave $ fromJust $ goUp loc

-- Update the current focus
update :: (a -> a) -> Loc a -> Loc a
update f (Loc hole ctxt) = Loc (f hole) ctxt

-- Generic Zipper class
class Zipper (f :: * -> *) a where
    -- Move focus to the leftmost recursive child, if possible
    first :: (a -> Ctxt f a -> b) -> f a -> Maybe b
    -- Move focus to the rightmost recursive child, if possible
    last  :: (a -> Ctxt f a -> b) -> f a -> Maybe b
    -- Plug a value into its context frame
    fill  :: a -> Ctxt f a -> f a
    -- Try to move focus one element to the left
    prev  :: (a -> Ctxt f a -> b) -> a -> Ctxt f a -> Maybe b
    -- Try to move focus one element to the right
    next  :: (a -> Ctxt f a -> b) -> a -> Ctxt f a -> Maybe b

-- ------------------------ Navigation functions
-- Move down
goDown :: Loc a -> Maybe (Loc a)
goDown (Loc hole ctxt) = first (\h c -> Loc h (Context c ctxt)) (from hole)

-- Move left
goLeft :: Loc a -> Maybe (Loc a)
goLeft (Loc _    CNil) = Nothing
goLeft (Loc hole (Context c ctxt))
                       = prev (\h c' -> Loc h (Context c' ctxt)) hole c

-- Move right
goRight :: Loc a -> Maybe (Loc a)
goRight (Loc _    CNil) = Nothing
goRight (Loc hole (Context c ctxt))
                        = next (\h c' -> Loc h (Context c' ctxt)) hole c

-- Move up
goUp :: Loc a -> Maybe (Loc a)
goUp (Loc _    CNil)             = Nothing
goUp (Loc hole (Context c ctxt)) = Just (Loc (to $ fill hole c) ctxt)

-- ------------------------ Implementation
data instance Ctxt (K b)     a
data instance Ctxt U         a
data instance Ctxt I         a = CI
data instance Ctxt (f :+: g) a = CL (Ctxt f a) | CR (Ctxt g a)
data instance Ctxt (f :*: g) a = C1 (Ctxt f a) (g a) | C2 (f a) (Ctxt g a)

instance Zipper (K b) a where
    first _ _   = Nothing
    last  _ _   = Nothing
    fill  _ _   = impossible
    prev  _ _ _ = impossible
    next  _ _ _ = impossible

instance Zipper U a where
    first _ _   = Nothing
    last  _ _   = Nothing
    fill  _ _   = impossible
    prev  _ _ _ = impossible
    next  _ _ _ = impossible

instance (Regular a, Zipper (PF a) a) => Zipper I a where
    first f (I x) = return (f x CI)
    last  f (I x) = return (f x CI)
    fill  x CI    = I x
    prev  _ _ _   = Nothing
    next  _ _ _   = Nothing

instance (Zipper f a, Zipper g a) => Zipper (f :+: g) a where
    first f (L x)    = first (\z c  -> f z (CL c)) x
    first f (R y)    = first (\z c  -> f z (CR c)) y
    last  f (L x)    = last  (\z c  -> f z (CL c)) x
    last  f (R y)    = last  (\z c  -> f z (CR c)) y
    fill  x (CL c)   = L (fill x c)
    fill  y (CR c)   = R (fill y c)
    prev  f x (CL c) = prev  (\z c' -> f z (CL c')) x c
    prev  f y (CR c) = prev  (\z c' -> f z (CR c')) y c
    next  f x (CL c) = next  (\z c' -> f z (CL c')) x c
    next  f y (CR c) = next  (\z c' -> f z (CR c')) y c

instance (Zipper f a, Zipper g a) => Zipper (f :*: g) a where
    first f (x :*: y)  = first (\z c  -> f z (C1 c y)) x
                 `mplus` first (\z c  -> f z (C2 x c)) y
    last  f (x :*: y)  = last  (\z c  -> f z (C2 x c)) y
                 `mplus` last  (\z c  -> f z (C1 c y)) x
    fill    x (C1 c y) = fill x c :*: y
    fill    y (C2 x c) = x :*: fill y c
    prev  f x (C1 c y) = prev  (\z c' -> f z (C1 c'          y)) x c
    prev  f y (C2 x c) = prev  (\z c' -> f z (C2 x          c')) y c
                 `mplus` last  (\z c' -> f z (C1 c' (fill y c))) x
    next  f x (C1 c y) = next  (\z c' -> f z (C1 c'          y)) x c
                 `mplus` first (\z c' -> f z (C2 (fill x c) c')) y
    next  f y (C2 x c) = next  (\z c' -> f z (C2 x          c')) y c

-- Internal error function
impossible :: a
impossible =  error "impossible"
