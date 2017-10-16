{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, MultiParamTypeClasses,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, PolyKinds,
    ConstraintKinds, ScopedTypeVariables, Rank2Types, GADTs,
    UndecidableSuperClasses, TypeApplications #-}
module GenericZipper where

import GHC.Exts (Constraint)
import Data.Maybe

import Generics.SOP

import Base
import GenericContext

----------------------------------------------------------------------------
--                     Generic zipper implementation
----------------------------------------------------------------------------
data Family (r :: *) (a :: *) (fam :: [*]) (c :: * -> Constraint) where
    Family :: (Generic b, Zipper fam c r a b, In b fam ~ 'True)
           => b -> Family r a fam c

class Proof (p :: Bool) (fam :: [*]) (c :: * -> Constraint)
            (r :: *) (a :: *) (b :: *) where
   witness :: Proxy p -> Fam fam c -> Proxy r -> Proxy a
           -> b -> Maybe (Family r a fam c)

instance Proof 'False fam c r a b where
   witness _ _ _ _ _ = Nothing
instance (Generic b, Zipper fam c r a b, In b fam ~ 'True)
       => Proof 'True fam c r a b where
   witness _ _ _ _   = Just . Family

type ProofIn fam c r a b = Proof (In b fam) fam c r a b

type family AllProof (fam :: [k]) (u :: k -> Constraint) (r :: k)
                    (a :: k) (xs :: [k]) :: Constraint where
   AllProof fam c r a '[] = ()
   AllProof fam c r a (x ': xs)
       = (ProofIn fam c r a x, AllProof fam c r a xs)

appToNP :: All2CFam2C c fam u r a xss
       => (forall xs. c fam u r a xs => Fam fam u -> Proxy r -> Proxy a
                                     -> NP I xs -> Maybe (Family r a fam u))
       -> Proxy c -> Fam fam u -> Proxy r -> Proxy a
       -> NS (NP I) xss -> Maybe (Family r a fam u)
appToNP f c pf pr p (S ns) = appToNP f c pf pr p ns
appToNP f _ pf pr p (Z np) = f pf pr p np

-- ------------------------------------------- toFirst
{-toFirst :: TreeIB -> TreeIB
toFirst (Leaf _)          = impossible
toFirst (TNode t _ _ _ _) = t
toFirst (BNode _ t _)     = t-}

toFirst :: (Generic a, ToFirst fam c r a)
        => Fam fam c -> Proxy r -> a -> Maybe (Family r a fam c)
toFirst pf pr (t :: a)
    = appToNP toFirstNP (Proxy @AllProof') pf pr (Proxy @a)
                        (unSOP $ from t)

class AllProof fam c r a xs => AllProof' fam c r a xs
instance AllProof fam c r a xs => AllProof' fam c r a xs

type ToFirst fam c r a = All2CFam2C AllProof' fam c r a (Code a)

toFirstNP :: AllProof fam c r a xs
          => Fam fam c -> Proxy r -> Proxy a
          -> NP I xs -> Maybe (Family r a fam c)
toFirstNP (pf :: Fam fam c) pr p (I (x :: b) :* xs)
    = fromMaybe (toFirstNP pf pr p xs)
                (case witness (Proxy @(In b fam)) pf pr p x of
                     Nothing -> Nothing
                     t       -> Just t)
toFirstNP _ _ _ Nil = Nothing

-- ------------------------------------------- toCtxFirst
{-toCtxFirst :: TreeIB -> GContext TreeIB
toCtxFirst (Leaf _)          = impossible
toCtxFirst (TNode _ m x y r) = from (TNode1 Proxy Hole m x y r)
toCtxFirst (BNode x _ r)     = from (BNode1 Proxy x Hole r)-}

toCtxFirst :: (Generic a, ToCtxFirst fam a)
           => Fam fam c -> a -> Context fam a
toCtxFirst pf (t :: a) = toCtxFirstNS pf (Proxy @a) (Proxy @'F)
                                      (unSOP $ from t)

type family CtxConsNum (xss :: [[k]]) (n :: ConsNum) :: ConsNum where
    CtxConsNum '[]                       n = 'None
    CtxConsNum ((Proxy n  ': xs) ': xss) n = 'F
    CtxConsNum ((Proxy n' ': xs) ': xss) n = 'N (CtxConsNum xss n)

class ConsNumInj (CtxConsNum (CtxCode fam a) n)
                 (Proxy n ': FstRecToHole fam xs)
    => CtxConsNInj n xs fam a
instance ConsNumInj (CtxConsNum (CtxCode fam a) n)
                    (Proxy n ': FstRecToHole fam xs)
    => CtxConsNInj n xs fam a

class AllProofF f (Proxy n ': FstRecToHole fam xs) yss
    => CtxAllProofF n f fam xs yss
instance AllProofF f (Proxy n ': FstRecToHole fam xs) yss
    => CtxAllProofF n f fam xs yss

class FromFstRec xs (FstRecToHole fam xs) => FromFstRec' fam xs
instance FromFstRec xs (FstRecToHole fam xs) => FromFstRec' fam xs

type ToCtxFirst' fam a n xss = (SListI (CtxCode fam a),
                                All2CFam FromFstRec' fam xss,
                                All2CN CtxConsNInj xss fam a n,
                                All2CFN2 CtxAllProofF
                                         (Injection (NP I)
                                         (CtxCode fam a))
                                         fam xss (CtxCode fam a) n)

type ToCtxFirst fam a = ToCtxFirst' fam a 'F (Code a)

toCtxFirstNS :: ToCtxFirst' fam a n xss
             => Fam fam c -> Proxy a -> Proxy (n :: ConsNum)
             -> NS (NP I) xss -> Context fam a
toCtxFirstNS pf p (_ :: Proxy n) (S ns)
    = toCtxFirstNS pf p (Proxy @('N n)) ns
toCtxFirstNS (pf :: Fam fam c) (p :: Proxy a) (_ :: Proxy n)
             (Z (np :: NP I xs))
    = appCtxInj pf p (Proxy @(CtxConsNum (CtxCode fam a) n))
                     (I (Proxy @n) :*
                      fromFstRec (Proxy @(FstRecToHole fam xs)) np)

-- ------------------------------------------- fillCtx
{-fillCtx :: GContext TreeIB -> TreeIB -> TreeIB
fillCtx tc t = case to tc of
    TNode1 _ _ m x y r -> TNode t m x y r
    TNode2 _ l _ x y r -> TNode l t x y r
    TNode3 _ l m x y _ -> TNode l m x y t
    BNode1 _ x _ r     -> BNode x t r
    BNode2 _ x l _     -> BNode x l t-}

fillCtx :: (Generic a, FillCtx fam a b,
            In a fam ~ 'True, Zipper fam c r x a)
        => Context fam a -> Proxy r -> Proxy x -> b -> Family r x fam c
fillCtx (c :: Context fam a) _ p (t :: b)
    = Family $ to @a $ fillCtxNS (Proxy @a) (unSOP $ ctx c) t

type family HoleToRec (xs :: [k]) (a :: k) :: [k] where
    HoleToRec (Proxy n ': xs) a = HoleToRec xs a
    HoleToRec (Hole    ': xs) a = a ': xs
    HoleToRec (x       ': xs) a = x ': HoleToRec xs a

class FillHole (xs :: [*]) (ys :: [*]) (a :: *) where
    fillHole :: Proxy ys -> NP I xs -> a -> NP I ys

instance FillHole xs ys a
        => FillHole (Proxy n ': xs) ys a where
    fillHole _ (_ :* xs)
        = fillHole (Proxy @ys) xs
instance FillHole (Hole ': ys) (y ': ys) y where
    fillHole _ (_ :* xs) t = I t :* xs
instance FillHole xs ys a
        => FillHole (y ': xs) (y ': ys) a where
    fillHole _ (x :* xs) t
        = x :* fillHole (Proxy @ys) xs t
instance FillHole '[] '[] a where
    fillHole _ _ _ = impossible

type family DataConsNum (xs :: [k]) :: ConsNum where
    DataConsNum (Proxy n ': xs) = n

class (FillHole xs (HoleToRec xs b) b,
       ConsNumInj (DataConsNum xs) (HoleToRec xs b),
       AllProofF (Injection (NP I) (Code a))
                 (HoleToRec xs b) (Code a))
    => FillCtx' a b xs

instance (FillHole xs (HoleToRec xs b) b,
          ConsNumInj (DataConsNum xs) (HoleToRec xs b),
          AllProofF (Injection (NP I) (Code a))
                    (HoleToRec xs b) (Code a))
    => FillCtx' a b xs

type FillCtx fam a b = All2C FillCtx' a b (CtxCode fam a)

fillCtxNS :: (SListI (Code a), All2C FillCtx' a b xss)
          => Proxy a -> NS (NP I) xss -> b -> Rep a
fillCtxNS p (S ns) t = fillCtxNS p ns t
fillCtxNS p (Z (np :: NP I xs)) (t :: b)
    = appInj p (Proxy @(DataConsNum xs))
               (fillHole (Proxy @(HoleToRec xs b)) np t)

-- ------------------------------------------- nextCtx
{-nextCtx :: GContext TreeIB -> TreeIB -> GContext TreeIB
nextCtx tc t = case to tc of
    TNode1 _ _ _ x y r -> from (TNode2 Proxy t Hole x y r)
    TNode2 _ l _ x y _ -> from (TNode3 Proxy l t x y Hole)
    TNode3{}           -> impossible
    BNode1 _ x _ _     -> from (BNode2 Proxy x t Hole)
    BNode2{}           -> impossible-}

nextCtx :: NextCtx fam a b => Context fam a -> b -> Context fam a
nextCtx (c :: Context fam a)
    = nextCtxNS (Fam @fam) (Proxy @a) (Proxy @'F) (unSOP $ ctx c)

type family ToNextHole (xs :: [k]) (fam :: [k]) (a :: k) :: [k] where
    ToNextHole (Proxy n ': xs) fam a = Proxy n ': ToNextHole xs fam a
    ToNextHole (Hole    ': xs) fam a = a       ': FstRecToHole fam xs
    ToNextHole (x       ': xs) fam a = x       ': ToNextHole xs fam a
    ToNextHole '[]             fam a = '[]

class NextHole (bs :: [Bool]) (xs :: [*]) (ys :: [*]) (a :: *) where
    nextHole :: Proxy bs -> Proxy ys -> NP I xs -> a -> NP I ys

instance FromFstRec xs ys
        => NextHole '[ 'True] (Hole ': xs) (y ': ys) y where
    nextHole _ _ (_ :* xs) t = I t :* fromFstRec (Proxy @ys) xs
instance NextHole bs xs ys a
        => NextHole ('False ': bs) (y ': xs) (y ': ys) a where
    nextHole _ _ (x :* xs) t
        = x :* nextHole (Proxy @bs) (Proxy @ys) xs t
instance NextHole '[] '[] '[] a where
    nextHole _ _ _ _ = impossible

class ConsNumInj n (ToNextHole xs fam a) => NextCtxConsNInj n xs fam a
instance ConsNumInj n (ToNextHole xs fam a) => NextCtxConsNInj n xs fam a

class (NextHole (IsHole xs) xs (ToNextHole xs fam b) b,
       AllProofF (Injection (NP I) (CtxCode fam a))
                 (ToNextHole xs fam b) (CtxCode fam a))
    => NextCtx'' fam a b xs

instance (NextHole (IsHole xs) xs (ToNextHole xs fam b) b,
          AllProofF (Injection (NP I) (CtxCode fam a))
                    (ToNextHole xs fam b) (CtxCode fam a))
    => NextCtx'' fam a b xs

type NextCtx' fam a b n xss = (SListI (CtxCode fam a),
                               All2CFam2 NextCtx'' fam a b xss,
                               All2CN NextCtxConsNInj xss fam b n)

type NextCtx fam a b = NextCtx' fam a b 'F (CtxCode fam a)

nextCtxNS :: NextCtx' fam a b n xss
          => Fam fam c -> Proxy a -> Proxy (n :: ConsNum)
          -> NS (NP I) xss -> b -> Context fam a
nextCtxNS pf p (_ :: Proxy n) (S ns) t
    = nextCtxNS pf p (Proxy @('N n)) ns t
nextCtxNS (pf :: Fam fam c) p (_ :: Proxy n)
          (Z (np :: NP I xs)) (t :: b)
    = appCtxInj pf p (Proxy @('N n))
                     (nextHole (Proxy @(IsHole xs))
                               (Proxy @(ToNextHole xs fam b)) np t)

-- ------------------------------------------- nextFromCtx
{-nextFromCtx :: GContext TreeIB -> TreeIB
nextFromCtx tc = case to tc of
    TNode1 _ _ t _ _ _ -> t
    TNode2 _ _ _ _ _ t -> t
    TNode3{}           -> impossible
    BNode1 _ _ _ t     -> t
    BNode2{}           -> impossible-}

nextFromCtx :: NextFromCtx fam c r a
            => Context fam a -> Proxy r -> Maybe (Family r a fam c)
nextFromCtx (c :: Context fam a) pr
    = appToNP nextFromCtxNP (Proxy @NextFromCtx') (Fam @fam) pr (Proxy @a)
                            (unSOP $ ctx c)

type family AfterHole (xs :: [k]) :: [k] where
    AfterHole (Hole ': xs) = xs
    AfterHole (x    ': xs) = AfterHole xs

class FindHole (bs :: [Bool]) (xs :: [*]) (ys :: [*]) where
    afterHole :: Proxy bs -> Proxy ys -> NP I xs -> NP I ys

instance FindHole bs xs ys => FindHole ('False ': bs) (x ': xs) ys where
    afterHole _ p (_ :* xs) = afterHole (Proxy @bs) p xs
instance FindHole '[ 'True] (Hole ': ys) ys where
    afterHole _ _ (_ :* xs) = xs

class (AllProof fam c r a (AfterHole xs),
       FindHole (IsHole xs) xs (AfterHole xs))
    => NextFromCtx' fam c r a xs
instance (AllProof fam c r a (AfterHole xs),
          FindHole (IsHole xs) xs (AfterHole xs))
    => NextFromCtx' fam c r a xs

type NextFromCtx fam c r a = All2CFam2C NextFromCtx' fam c r a (CtxCode fam a)

nextFromCtxNP :: NextFromCtx' fam c r a xs
              => Fam fam c -> Proxy r -> Proxy a
              -> NP I xs -> Maybe (Family r a fam c)
nextFromCtxNP pf pr p (ys :: NP I xs)
    = toFirstNP pf pr p $ afterHole (Proxy @(IsHole xs))
                                    (Proxy @(AfterHole xs)) ys

-- ------------------------------------------- Navigation functions
data Contexts (r :: *) (a :: *) (fam :: [*]) (c :: * -> Constraint) where
    CNil :: Contexts a a fam c
    Ctxs :: (Generic a, In a fam ~ 'True, c a, Zipper fam c r x a)
         => Context fam a -> Contexts r x fam c -> Contexts r a fam c

data Loc (r :: *) (fam :: [*]) (c :: * -> Constraint) where
    Loc :: Family r a fam c -> Contexts r a fam c -> Loc r fam c

type GoDown  fam c r a   = (ToFirst fam c r a, ToCtxFirst fam a)
type GoRight fam c r a b = (NextCtx fam a b, NextFromCtx fam c r a)
type GoUp    fam a b     = FillCtx fam a b

type Zipper fam c r a b
    = (GoDown fam c r b, GoRight fam c r a b, GoUp fam a b,
       ProofEq r b, c b)

goDown :: Loc a fam c -> Maybe (Loc a fam c)
goDown (Loc (Family t) cs :: Loc a fam c)
    = case toFirst (Fam @fam) (Proxy @a) t of
        Just t' -> Just $ Loc t' (Ctxs (toCtxFirst (Fam @fam) t) cs)
        _       -> Nothing

goRight :: Loc a fam c -> Maybe (Loc a fam c)
goRight (Loc _ CNil) = Nothing
goRight (Loc (Family t) (Ctxs c cs) :: Loc a fam c)
    = case nextFromCtx c (Proxy @a) of
        Just t' -> Just (Loc t' (Ctxs (nextCtx c t) cs))
        _       -> Nothing

goUp :: Loc a fam c -> Maybe (Loc a fam c)
goUp (Loc _ CNil) = Nothing
goUp (Loc (Family t) (Ctxs c (cs :: Contexts a x fam c)))
    = Just (Loc (fillCtx c (Proxy @a) (Proxy @x) t) cs)

-- Start navigating
enter :: (Generic a, In a fam ~ 'True, Zipper fam c a a a)
      => Fam fam c -> a -> Loc a fam c
enter (_ :: Fam fam c) (hole :: a) = Loc (Family hole) (CNil @a @fam @c)

-- End navigating
leave :: Loc a fam c -> a
leave (Loc (Family (hole :: b) :: Family a x fam c) CNil)
    = fromJust $ witnessEq (Proxy @(Equal a b)) (Proxy @a) hole
leave loc = leave $ fromJust $ goUp loc

-- Update the current focus
update :: (forall b. c b => b -> b) -> Loc a fam c -> Loc a fam c
update f (Loc (Family hole) cs) = Loc (Family (f hole)) cs

-- Flipped function composition
(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) f g = g . f
