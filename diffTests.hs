{-# LANGUAGE DataKinds, TypeOperators #-}
module DiffTests where

import TreeZipper
import GenericContext
import Generics.SOP

data Tree' = BNode' Int Tree' Tree' | MNode' Char Tree' | Leaf'

type Test = ToContext Tree' '[ '[Int, Tree', Tree'], '[]]

test :: NS (NP I) Test
test = Z (I 5 :* I Leaf' :* Nil)

type Test' = '[Int, Tree'] .** ('[ '[]] .++ '[ '[]])

test' :: NS (NP I) Test'
test' = Z (I 5 :* I Leaf' :* Nil)

type Test'' = DiffProd Tree' '[Tree', Tree']

test'' :: NS (NP I) Test''
test'' = Z (I Leaf' :* Nil)

type Test''' = ToContext Tree' '[ '[Int, Tree', Tree'], '[Char, Tree'], '[]]

test1 :: NS (NP I) Test'''
test1 = Z (I 5 :* I Leaf' :* Nil)

test2 :: NS (NP I) Test'''
test2 = S (S (Z (I 'a' :* Nil)))

type GTreeCtx' a b = ToContext (Tree a b) (Code (Tree a b))

testTree1 :: NS (NP I) (GTreeCtx' Int Char)
testTree1 = Z (I (Leaf 2) :* I 5 :* I 'b' :* I (Leaf 2) :* Nil)
testTree2 :: NS (NP I) (GTreeCtx' Int Char)
testTree2 = S (Z (I (Leaf 2) :* I 5 :* I 'b' :* I (Leaf 2) :* Nil))
testTree3 :: NS (NP I) (GTreeCtx' Int Char)
testTree3 = S (S (Z (I (Leaf 2) :* I (Leaf 2) :* I 5 :* I 'b' :* Nil)))
testTree4 :: NS (NP I) (GTreeCtx' Int Char)
testTree4 = S (S (S (Z (I 'a' :* I (Leaf 2) :* Nil))))
testTree5 :: NS (NP I) (GTreeCtx' Int Char)
testTree5 = S (S (S (S (Z (I 'a' :* I (Leaf 2) :* Nil)))))
