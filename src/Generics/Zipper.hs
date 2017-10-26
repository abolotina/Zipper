-- | The main module of the @generic-zipper@ library.
--
-- = Example
--
-- Let us consider the example of a family of mutually recursive datatypes.
--
-- @
--  data Expr = Const Int
--            | Add Expr Expr
--            | Mul Expr Expr
--            | EVar Var
--            | Let Decl Expr
--  data Decl = Var := Expr
--            | Seq Decl Decl
--  type Var  = String
-- @
--
-- To use the Zipper interface, you need to create 'Generics.SOP.Generic'
-- instances for these datatypes. It is possible to derive the instances
-- via the built-in GHC-generics:
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- >
-- > import Generics.SOP
-- > import qualified GHC.Generics as GHC (Generic)
-- >
-- > data Expr = Const Int
-- >           | Add Expr Expr
-- >           | Mul Expr Expr
-- >           | EVar Var
-- >           | Let Decl Expr
-- >     deriving (GHC.Generic, Show)
-- > data Decl = Var := Expr
-- >           | Seq Decl Decl
-- >     deriving (GHC.Generic, Show)
-- > type Var  = String
--
-- Then, we can just say:
--
-- @
-- instance Generic Expr
-- instance Generic Decl
-- @
--
-- Assume we want to traverse the following example expression
-- using the Zipper.
--
-- @
-- example :: Expr
-- example = Let ("x" := Mul (Const 6) (Const 9))
--               (Add (EVar "x") (EVar "y"))
-- @
--
-- Let us define a class that provides a function for updating the tree.
--
-- @
-- class Update a where
--     solve :: a -> a
--     solve = id
-- instance Update Expr where
--     solve _ = Const 42
-- instance Update Decl
-- instance Update Var
-- @
--
-- == Using the Zipper
--
-- A type for a family of mutually recursive datatypes is a promoted list
-- of types that you consider as mutually recursive,
-- fixed by the datatype 'Fam':
--
-- @
--   data Fam (fam :: [*]) (c :: * -> Constraint) = Fam
-- @
--
-- The parameter @c@ is needed to fix all constraints, applied to each
-- datatype in the family.
--
-- The flipped function composition '>>>' and flipped Kleisli (monadic)
-- composition '>=>' are helpful to combine the navigation and
-- edit operations.
--
-- @
-- type ExampleFam1 = '[Expr, Decl, Var]
--
-- test1 = enter (Fam \@ExampleFam1 \@Update)
--             >>> goDown >=> goDown >=> goRight >=> update solve
--             >>> leave >>> return $ example
-- @
--
-- Note that the code above requires the @TypeApplications@ extension.
-- You may substitute for:
--
-- > (Fam :: Fam ExampleFam Update)
--
-- Defining another example of a traversal on this value should show that
-- using the generic Zipper is flexible for families of mutually recursive
-- datatypes.
--
-- @
-- type ExampleFam2 = '[Expr, Var]
--
-- test2 = enter (Fam \@ExampleFam2 \@Update)
--             >>> goDown >=> goDown >=> goRight >=> update solve
--             >>> leave >>> return $ example
-- @
--
-- The calls of these two tests will yield the desired results:
--
-- >>> test1
-- Just (Let ("x" := Const 42) (Add (EVar "x") (EVar "y")))
-- >>> test2
-- Just (Let ("x" := Mul (Const 6) (Const 9)) (Add (EVar "x") (Const 42)))
--
module Generics.Zipper (
    -- * Locations
    Loc
    -- * Families
  , Fam(..)
    -- * Interface
    -- ** Navigation functions
  , goDown
  , goRight
  , goUp
    -- ** Start navigating
  , enter
    -- ** End navigating
  , leave
    -- ** Updating
  , update
    -- * Combining operations
  , (>>>)
    -- ** Re-exports
  , (>=>)
) where

import Control.Monad ((>=>))

import Generics.Zipper.Base
import Generics.Zipper.GenericContext
import Generics.Zipper.GenericZipper
