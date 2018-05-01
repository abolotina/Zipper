{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, Rank2Types, GADTs,
    UndecidableSuperClasses, TypeApplications, AllowAmbiguousTypes #-}
-- | This module provides the implementation of the top-level zipper
-- operations and exports the zipper interface functions.
--
-- For more datailed documentation, see the "Generics.Zipper" module.
--
module Generics.Zipper.GenericZipper (
    -- * Locations
    Loc
    -- * Interface
    -- ** Movement functions
  , goDown
  , goRight
  , goUp
    -- ** Starting navigation
  , enter
    -- ** Ending navigation
  , leave
    -- ** Updating
  , update
    -- * Combining operations
  , (>>>)
) where

import GHC.Exts (Constraint)
import Data.Maybe
import Control.Monad

import Generics.Zipper.Base
import Generics.Zipper.GenericContext

----------------------------------------------------------------------------
--                     Generic zipper implementation
----------------------------------------------------------------------------
data Family (r :: *) (a :: *) (fam :: [*]) (c :: * -> Constraint) where
    Family :: (Generic b, ZipperI fam r a b c, In b fam)
           => b -> Family r a fam c

class Proof (inFam :: Bool) (fam :: [*]) (c :: * -> Constraint)
            (r :: *) (a :: *) (b :: *) where
   witness :: b -> Maybe (Family r a fam c)

instance Proof 'False fam c r a b where
   witness _ = Nothing
instance (Generic b, ZipperI fam r a b c, In b fam)
       => Proof 'True fam c r a b where
   witness   = Just . Family

class Proof (InFam b fam) fam c r a b => ProofIn fam c r a b
instance Proof (InFam b fam) fam c r a b => ProofIn fam c r a b

appToNP :: forall c fam u r a xss. All (c fam u r a) xss
        => (forall xs. c fam u r a xs => NP I xs -> Maybe (Family r a fam u))
        -> NS (NP I) xss -> Maybe (Family r a fam u)
appToNP f (S ns) = appToNP @c f ns
appToNP f (Z np) = f np

-- ------------------------------------------- toFirst
{-toFirst :: TreeIB -> TreeIB
toFirst (Leaf _)          = impossible
toFirst (TNode t _ _ _ _) = t
toFirst (BNode _ t _)     = t-}

toFirst :: forall fam c r a. (Generic a, ToFirst fam c r a)
        => a -> Maybe (Family r a fam c)
toFirst t = appToNP @AllProof toFirstNP $ unSOP $ from t

class All (ProofIn fam c r a) xs => AllProof fam c r a xs
instance All (ProofIn fam c r a) xs => AllProof fam c r a xs

type ToFirst fam c r a = All (AllProof fam c r a) (Code a)

toFirstNP :: forall fam c r a xs. All (ProofIn fam c r a) xs
          => NP I xs -> Maybe (Family r a fam c)
toFirstNP (I (x :: b) :* xs)
    = witness @(InFam b fam) x `mplus` toFirstNP xs
toFirstNP Nil = Nothing

-- ------------------------------------------- toCtxFirst
{-toCtxFirst :: TreeIB -> GContext TreeIB
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = from (TNode1 Proxy Hole m x y r)
toCtxFirst (BNode x _ r)     = from (BNode1 Proxy x Hole r)-}

toCtxFirst :: forall fam c a. (Generic a, ToCtxFirst fam a)
           => a -> Context fam a
toCtxFirst t = toCtxFirstNS @'F $ unSOP $ from t

type family CtxConsNum (code :: [[*]]) (n :: ConsNum) :: ConsNum where
    CtxConsNum '[]                       n = 'None
    CtxConsNum ((Proxy n  ': xs) ': xss) n = 'F
    CtxConsNum ((Proxy n' ': xs) ': xss) n = 'N (CtxConsNum xss n)

type FstCtx n fam xs = Proxy n ': FstRecToHole fam xs

class ConsNumInj (CtxConsNum (CtxCode fam a) n) (FstCtx n fam xs)
    => CtxConsNInj fam a xs n
instance ConsNumInj (CtxConsNum (CtxCode fam a) n) (FstCtx n fam xs)
    => CtxConsNInj fam a xs n

class All (ProofF f (FstCtx n fam xs)) yss
    => CtxAllProofF f fam yss xs n
instance All (ProofF f (FstCtx n fam xs)) yss
    => CtxAllProofF f fam yss xs n

class FromFstRec (FstRecToHole fam xs) xs => FromFstRec' fam xs
instance FromFstRec (FstRecToHole fam xs) xs => FromFstRec' fam xs

type ToCtxFirst' fam a n xss = (SListI (CtxCode fam a),
                                All (FromFstRec' fam) xss,
                                AllNum (CtxConsNInj fam a) xss n,
                                AllNum (CtxAllProofF
                                          (Injection (NP I) (CtxCode fam a))
                                          fam (CtxCode fam a)) xss n)

type ToCtxFirst fam a = ToCtxFirst' fam a 'F (Code a)

toCtxFirstNS :: forall n fam a xss. ToCtxFirst' fam a n xss
             => NS (NP I) xss -> Context fam a
toCtxFirstNS (S ns) = toCtxFirstNS @('N n) ns
toCtxFirstNS (Z (np :: NP I xs))
    = appCtxInj @(CtxConsNum (CtxCode fam a) n) $
                I (Proxy @n) :* fromFstRec @(FstRecToHole fam xs) np

-- ------------------------------------------- fillCtx
{-fillCtx :: GContext TreeIB -> TreeIB -> TreeIB
fillCtx tc t = case to tc of
    TNode1 _ _ m x y r -> TNode t m x y r
    TNode2 _ l _ x y r -> TNode l t x y r
    TNode3 _ l m x y _ -> TNode l m x y t
    BNode1 _ x _ r     -> BNode x t r
    BNode2 _ x l _     -> BNode x l t-}

fillCtx :: forall r x fam a b c.
           (Generic a, FillCtx fam a b, In a fam, ZipperI fam r x a c)
        => Context fam a -> b -> Family r x fam c
fillCtx c t = Family $ to @a $ fillCtxNS @a (unSOP $ ctx c) t

type family HoleToRec (xs :: [k]) (a :: k) :: [k] where
    HoleToRec (Proxy n ': xs) a = HoleToRec xs a
    HoleToRec (Hole    ': xs) a = a ': xs
    HoleToRec (x       ': xs) a = x ': HoleToRec xs a

class FillHole (ys :: [*]) (xs :: [*]) (a :: *) where
    fillHole :: NP I xs -> a -> NP I ys

instance FillHole ys xs a
        => FillHole ys (Proxy n ': xs) a where
    fillHole (_ :* xs) = fillHole xs
instance FillHole (y ': ys) (Hole ': ys) y where
    fillHole (_ :* xs) t = I t :* xs
instance FillHole ys xs a
        => FillHole (y ': ys) (y ': xs) a where
    fillHole (x :* xs) t = x :* fillHole xs t
instance FillHole '[] '[] a where
    fillHole _ _ = impossible

type family DataConsNum (xs :: [k]) :: ConsNum where
    DataConsNum (Proxy n ': xs) = n

class (FillHole (HoleToRec xs b) xs b,
       ConsNumInj (DataConsNum xs) (HoleToRec xs b),
       All (ProofF (Injection (NP I) (Code a)) (HoleToRec xs b))
           (Code a))
    => FillCtx' a b xs

instance (FillHole (HoleToRec xs b) xs b,
          ConsNumInj (DataConsNum xs) (HoleToRec xs b),
          All (ProofF (Injection (NP I) (Code a)) (HoleToRec xs b))
              (Code a))
    => FillCtx' a b xs

type FillCtx fam a b = All (FillCtx' a b) (CtxCode fam a)

fillCtxNS :: forall a b xss. (SListI (Code a), All (FillCtx' a b) xss)
          => NS (NP I) xss -> b -> Rep a
fillCtxNS (S ns) t = fillCtxNS @a ns t
fillCtxNS (Z (np :: NP I xs)) t
    = appInj @a @(DataConsNum xs) $ fillHole @(HoleToRec xs b) np t

-- ------------------------------------------- nextCtx
{-nextCtx :: GContext TreeIB -> TreeIB -> GContext TreeIB
nextCtx tc t = case to tc of
    TNode1 _ _ _ x y r -> from (TNode2 Proxy t Hole x y r)
    TNode2 _ l _ x y _ -> from (TNode3 Proxy l t x y Hole)
    TNode3{}           -> impossible
    BNode1 _ x _ _     -> from (BNode2 Proxy x t Hole)
    BNode2{}           -> impossible-}

nextCtx :: forall fam a b. NextCtx fam a b
        => Context fam a -> b -> Context fam a
nextCtx c = nextCtxNS @'F (unSOP $ ctx c)

type family ToNextHole (xs :: [k]) (fam :: [k]) (a :: k) :: [k] where
    ToNextHole (Proxy n ': xs) fam a = Proxy n ': ToNextHole xs fam a
    ToNextHole (Hole    ': xs) fam a = a       ': FstRecToHole fam xs
    ToNextHole (x       ': xs) fam a = x       ': ToNextHole xs fam a
    ToNextHole '[]             fam a = '[]

class NextHole (bs :: [Bool]) (ys :: [*]) (xs :: [*]) (a :: *) where
    nextHole :: NP I xs -> a -> NP I ys

instance FromFstRec ys xs
        => NextHole '[ 'True] (y ': ys) (Hole ': xs) y where
    nextHole (_ :* xs) t = I t :* fromFstRec @ys xs
instance NextHole bs ys xs a
        => NextHole ('False ': bs) (y ': ys) (y ': xs) a where
    nextHole (x :* xs) t = x :* nextHole @bs @ys xs t
instance NextHole '[] '[] '[] a where
    nextHole _         _ = impossible

class ConsNumInj n (ToNextHole xs fam a) => NextCtxConsNInj fam a xs n
instance ConsNumInj n (ToNextHole xs fam a) => NextCtxConsNInj fam a xs n

class (NextHole (IsHole xs) (ToNextHole xs fam b) xs b,
       All (ProofF (Injection (NP I) (CtxCode fam a))
                   (ToNextHole xs fam b))
           (CtxCode fam a))
    => NextCtx'' fam a b xs

instance (NextHole (IsHole xs) (ToNextHole xs fam b) xs b,
          All (ProofF (Injection (NP I) (CtxCode fam a))
                      (ToNextHole xs fam b))
              (CtxCode fam a))
    => NextCtx'' fam a b xs

type NextCtx' fam a b n xss = (SListI (CtxCode fam a),
                               All (NextCtx'' fam a b) xss,
                               AllNum (NextCtxConsNInj fam b) xss n)

type NextCtx fam a b = NextCtx' fam a b 'F (CtxCode fam a)

nextCtxNS :: forall n fam a b xss. NextCtx' fam a b n xss
          => NS (NP I) xss -> b -> Context fam a
nextCtxNS (S ns) t = nextCtxNS @('N n) ns t
nextCtxNS (Z (np :: NP I xs)) t
    = appCtxInj @('N n) $ nextHole @(IsHole xs)
                                   @(ToNextHole xs fam b) np t

-- ------------------------------------------- nextFromCtx
{-nextFromCtx :: GContext TreeIB -> TreeIB
nextFromCtx tc = case to tc of
    TNode1 _ _ t _ _ _ -> t
    TNode2 _ _ _ _ _ t -> t
    TNode3{}           -> impossible
    BNode1 _ _ _ t     -> t
    BNode2{}           -> impossible-}

nextFromCtx :: NextFromCtx fam c r a
            => Context fam a -> Maybe (Family r a fam c)
nextFromCtx c = appToNP @NextFromCtx' nextFromCtxNP $ unSOP $ ctx c

type family AfterHole (xs :: [k]) :: [k] where
    AfterHole (Hole ': xs) = xs
    AfterHole (x    ': xs) = AfterHole xs

class FindHole (bs :: [Bool]) (ys :: [*]) (xs :: [*]) where
    afterHole :: NP I xs -> NP I ys

instance FindHole bs ys xs => FindHole ('False ': bs) ys (x ': xs) where
    afterHole (_ :* xs) = afterHole @bs xs
instance FindHole '[ 'True] ys (Hole ': ys) where
    afterHole (_ :* xs) = xs

class (All (ProofIn fam c r a) (AfterHole xs),
       FindHole (IsHole xs) (AfterHole xs) xs)
    => NextFromCtx' fam c r a xs
instance (All (ProofIn fam c r a) (AfterHole xs),
          FindHole (IsHole xs) (AfterHole xs) xs)
    => NextFromCtx' fam c r a xs

type NextFromCtx fam c r a = All (NextFromCtx' fam c r a) (CtxCode fam a)

nextFromCtxNP :: forall fam c r a xs. NextFromCtx' fam c r a xs
              => NP I xs -> Maybe (Family r a fam c)
nextFromCtxNP ys = toFirstNP $ afterHole @(IsHole xs) @(AfterHole xs) ys

-- ------------------------------------------- Navigation functions
data Contexts (r :: *) (a :: *) (fam :: [*]) (c :: * -> Constraint) where
    CNil :: Contexts a a fam c
    Ctxs :: (Generic a, In a fam, ZipperI fam r x a c)
         => Context fam a -> Contexts r x fam c -> Contexts r a fam c

-- | A location contains the current focus and its context.
-- Its type fixes the type of the root, the type of the family
-- of datatypes, and the constraint over datatypes in the family.
data Loc (r :: *) (fam :: [*]) (c :: * -> Constraint) where
    Loc :: Family r a fam c -> Contexts r a fam c -> Loc r fam c

type GoDown  fam c r a   = (ToFirst fam c r a, ToCtxFirst fam a)
type GoRight fam c r a b = (NextCtx fam a b, NextFromCtx fam c r a)
type GoUp    fam a b     = FillCtx fam a b

type ZipperI fam r a b c
    = (GoDown fam c r b, GoRight fam c r a b, GoUp fam a b,
       ProofEq r b, c b)
type Zipper a fam c = ZipperI fam a a a c

-- | Move down to the leftmost child if possible. For leaves,
-- return 'Nothing'.
goDown :: Loc a fam c -> Maybe (Loc a fam c)
goDown (Loc (Family t) cs)
    = case toFirst t of
        Just t' -> Just $ Loc t' (Ctxs (toCtxFirst t) cs)
        _       -> Nothing

-- | Move down to the right sibling if possible, else return 'Nothing'.
goRight :: Loc a fam c -> Maybe (Loc a fam c)
goRight (Loc _ CNil) = Nothing
goRight (Loc (Family t) (Ctxs c cs))
    = case nextFromCtx c of
        Just t' -> Just (Loc t' (Ctxs (nextCtx c t) cs))
        _       -> Nothing

-- | Move down to the parent if possible. For the root, return 'Nothing'.
goUp :: Loc a fam c -> Maybe (Loc a fam c)
goUp (Loc _ CNil) = Nothing
goUp (Loc (Family t) (Ctxs c cs))
    = Just (Loc (fillCtx c t) cs)

-- | Enter a tree. Places the value into the empty context.
enter :: forall fam c a. (Generic a, In a fam, Zipper a fam c)
      => a -> Loc a fam c
enter hole = Loc (Family hole) CNil

-- | Move up to the root and return the expression in focus.
leave :: Loc a fam c -> a
leave (Loc (Family (hole :: b) :: Family a x fam c) CNil)
    = fromJust $ witnessEq @(Equal a b) hole
leave loc = leave $ fromJust $ goUp loc

-- | Update the current focus, which contains a constrained value.
update :: (forall b. c b => b -> b) -> Loc a fam c -> Loc a fam c
update f (Loc (Family hole) cs) = Loc (Family (f hole)) cs

-- | Flipped function composition.
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) f g = g . f
