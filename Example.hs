{-# LANGUAGE DataKinds, TypeApplications, TypeSynonymInstances,
    FlexibleInstances, DeriveGeneric #-}

module Example where

import Control.Monad

import Generics.SOP
import qualified GHC.Generics as GHC (Generic)

import Base
import GenericZipper

-- An example of a family of mutually recursive datatypes
data Expr = Const Int
          | Add Expr Expr
          | Mul Expr Expr
          | EVar Var
          | Let Decl Expr
    deriving (GHC.Generic, Show)
data Decl = Var := Expr
          | Seq Decl Decl
    deriving (GHC.Generic, Show)
type Var  = String

instance Generic Expr
instance Generic Decl

-- An example value of Expr
example :: Expr
example = Let ("x" := Mul (Const 6) (Const 9))
              (Add (EVar "x") (EVar "y"))

-- This class provides a function for updating the tree
class Update a where
    solve :: a -> a
    solve = id
instance Update Expr where
    solve _ = Const 42
instance Update Decl
instance Update Var

-- An example of using the generic zipper

-- A type for a family of mutually recursive datatypes is a promoted list
-- of types that you consider as mutually recursive,
-- fixed by the datatype 'Fam':

-- @
--   data Fam (fam :: [*]) (c :: * -> Constraint) = Fam
-- @

-- The parameter 'c' is needed to fix all constraints, applied to each
-- datatype in the family.

-- The flipped function composition '>>>' and flipped kleisli (monadic)
-- composition '>=>' are helpful to combine the navigation and
-- edit operations.

-- The following code requires the 'TypeApplications' extension.
-- You may substitute for @(Fam :: Fam ExampleFam Update)@.

type ExampleFam1 = '[Expr, Decl, Var]

test1 = enter (Fam @ExampleFam1 @Update)
            >>> goDown >=> goDown >=> goRight >=> update solve
            >>> leave >>> return $ example

-- The result is
-- Just (Let ("x" := Const 42) (Add (EVar "x") (EVar "y")))

type ExampleFam2 = '[Expr, Var]

test2 = enter (Fam @ExampleFam2 @Update)
            >>> goDown >=> goDown >=> goRight >=> update solve
            >>> leave >>> return $ example

-- The result is
-- Just (Let ("x" := Mul (Const 6) (Const 9)) (Add (EVar "x") (Const 42)))
