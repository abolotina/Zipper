{-# LANGUAGE DataKinds, KindSignatures, PolyKinds,
    TypeOperators, TypeFamilies, FlexibleInstances, ConstraintKinds,
    FlexibleContexts, MultiParamTypeClasses, UndecidableInstances,
    TypeApplications, ScopedTypeVariables, UndecidableSuperClasses #-}
-- | Generic show.
--
-- = Example
--
-- To use the 'gShow' function, you need to create 'Generics.SOP.Generic'
-- instances for your datatypes.
--
-- Consider as an example the datatype for binary trees.
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- >
-- > import Generics.SOP
-- > import qualified GHC.Generics as GHC (Generic)
-- >
-- > data BinTree a = Leaf a | Node (BinTree a) (BinTree a)
-- >     deriving GHC.Generics
-- >
-- > instance Generic (BinTree a)
--
-- Look at such the expression of this type.
--
-- @
-- treeExample :: BinTree Int
-- treeExample = Node (Leaf 13) (Node (Leaf 42) (Leaf 777))
-- @
--
-- The result of the 'gShow' call is the same as for the call of the 'show'
-- function you can get via 'deriving Show'.
--
-- >>> gShow treeExample
-- "Node (Leaf 13) (Node (Leaf 42) (Leaf 777))"
--
module Generics.GShow (gShow) where

import GHC.Exts (Constraint)
import Data.List (intercalate)

import Generics.Zipper.Base

-------------------------------------------------
--                                   Generic show
-------------------------------------------------

-- | A generic show function defined using @generics-sop@.
--
-- This function is an improved version of 'Generics.SOP.Show.gshow'
-- from the @basic-sop@ package.
--
-- You may use it as a replacement for the 'show' function you get by using
-- 'deriving Show'.
gShow :: GShow a => a -> String
gShow (t :: a) = gShow' pa (constructorInfo $ datatypeInfo pa) (from t)
  where
    pa = Proxy @a

class CaseShow (p :: Bool) (a :: *) (b :: *) where
    caseShow' :: Proxy p -> Proxy a -> b -> String

instance Show b => CaseShow 'False a b where
    caseShow' _ _ = show
instance GShow a => CaseShow 'True a a where
    caseShow' _ _ t = "(" ++ gShow t ++ ")"

class CaseShow (Equal a b) a b => CaseRecShow a b
instance CaseShow (Equal a b) a b => CaseRecShow a b

type GShow a = (Generic a, HasDatatypeInfo a, All2 (CaseRecShow a) (Code a))

caseShow :: CaseRecShow a b => Proxy a -> b -> String
caseShow (_ :: Proxy a) (t :: b)
    = caseShow' (Proxy @(Equal a b)) (Proxy @a) t

gShow' :: (All2 (CaseRecShow a) xss, SListI xss)
       => Proxy a -> NP ConstructorInfo xss -> SOP I xss -> String
gShow' (pa :: Proxy a) cs (SOP sop)
    = hcollapse $ hcliftA2 allp (goConstructor pa) cs sop
  where
    allp = Proxy @(All (CaseRecShow a))

goConstructor :: All (CaseRecShow a) xs
    => Proxy a -> ConstructorInfo xs -> NP I xs -> K String xs
goConstructor (pa :: Proxy a) (Constructor n) args =
    K $ unwords (n : args')
  where
    args' :: [String]
    args' = hcollapse $
              hcliftA (Proxy @(CaseRecShow a)) (K . caseShow pa . unI) args

goConstructor (pa :: Proxy a) (Record n ns) args =
    K $ n ++ " {" ++ intercalate ", " args' ++ "}"
  where
    args' :: [String]
    args' = hcollapse $
              hcliftA2 (Proxy @(CaseRecShow a)) (goField pa) ns args

goConstructor pa (Infix n _ _) (I arg1 :* I arg2 :* Nil) =
    K $ caseShow pa arg1 ++ " " ++ n ++ " " ++ caseShow pa arg2

goField :: (CaseRecShow a) x
        => Proxy a -> FieldInfo x -> I x -> K String x
goField pa (FieldInfo field) (I a) = K $ field ++ " = " ++ caseShow pa a
