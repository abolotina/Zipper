# The generic zipper for mutually recursive datatypes

The zipper is a data structure that enables efficient navigation and editing
within the tree-like structure of a datatype. It represents a current location
in that structure, storing a tree node, a _focus_, along with its context.

The zipper interface comprises the functions for _movement_, _starting_ and
_ending_ navigation, and _updating_ the focus.

The module [Generics.Zipper](src/Generics/Zipper.hs) is the main module.
It provides documentation of the library.

## Example

Let us consider the example of a family of mutually recursive datatypes.

```haskell
data Expr = Const Int
          | Add Expr Expr
          | Mul Expr Expr
          | EVar Var
          | Let Decl Expr
data Decl = Var := Expr
          | Seq Decl Decl
type Var  = String
```

To use the zipper interface for these datatypes, you need to create
instances of the `Generic` class from the
[generics-sop](https://hackage.haskell.org/package/generics-sop) library.
It is possible to derive the instances via `GHC.Generics`:

```haskell
{-# LANGUAGE DeriveGeneric #-}

import Generics.SOP
import qualified GHC.Generics as GHC (Generic)

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
```

Assume we want to traverse the following example expression
using the zipper.

```haskell
example :: Expr
example = Let ("x" := Mul (Const 6) (Const 9))
              (Add (EVar "x") (EVar "y"))
```

Let us define a class that provides a function for updating the tree.

```haskell
class Update a where
    solve :: a -> a
    solve = id
instance Update Expr where
    solve _ = Const 42
instance Update Decl
instance Update Var
```

## Using the Zipper

A type for a family of mutually recursive datatypes is a promoted list
of types that you consider as mutually recursive:

```haskell
type ExampleFam1 = '[Expr, Decl, Var]
```

The flipped function composition `>>>` and flipped Kleisli (monadic)
composition `>=>` can be used to chain moves and
edit operations. In the following definition of `test1`, `enter`
starts navigation within the tree-like structure of the expression;
the `enter` function takes two type arguments: a family of datatypes
and a (single or complex) constraint that is meant to be applied to each
datatype in the family (such as `Update` in our example).

```haskell
test1 = enter @ExampleFam1 @Update
            >>> goDown >=> goDown >=> goRight >=> update solve
            >>> leave >>> return $ example
```

The code above uses the `TypeApplications` extension.

Defining another example of traversal with this value shows that
usage of the generic zipper is meant to be flexible for various families
of mutually recursive datatypes.

```haskell
type ExampleFam2 = '[Expr, Var]

test2 = enter @ExampleFam2 @Update
            >>> goDown >=> goDown >=> goRight >=> update solve
            >>> leave >>> return $ example
```

The calls of these two tests yield the following results:

```
*Main> test1

Just (Let ("x" := Const 42) (Add (EVar "x") (EVar "y")))

*Main> test2

Just (Let ("x" := Mul (Const 6) (Const 9)) (Add (EVar "x") (Const 42)))
```
