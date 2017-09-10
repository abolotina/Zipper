{-# LANGUAGE DataKinds, TypeOperators #-}
module DiffTests where

import Generics.SOP

import TreeExample
import GenericContext

type ExampleSum  = '[ '[Int, Bool]] .++ '[ '[Char, Bool, Int], '[Int]]
type ExampleSum' = '[ '[Int, Bool], '[Char, Bool, Int], '[Int]]

testSum0, testSum2 :: NS (NP I) ExampleSum'
testSum0 = Z (I 5 :* I True :* Nil)
testSum2 = S (S (Z (I 5 :* Nil)))

type ExampleProd  = Int .* '[ '[Int, Bool], '[Char]]
type ExampleProd' = '[ '[Int, Int, Bool], '[Int, Char]]

type ProdUnit  = Char .* ('[ '[]])
type ProdUnit' = '[ '[Char]]

type ProdZero  = Int .* '[]
type ProdZero' = '[]

type ExamplePProd  = '[Int, Bool] .** '[ '[Bool], '[Bool, Char]]
type ExamplePProd' = '[ '[Int, Bool, Bool], '[Int, Bool, Bool, Char]]

testProdUnit0 :: NS (NP I) ProdUnit'
testProdUnit0 = Z (I 'x' :* Nil)

testPProd0, testPProd1 :: NS (NP I) ExamplePProd
testPProd0 = Z (I 5 :* I False :* I True :* Nil)
testPProd1 = S (Z (I 5 :* I False :* I True :* I 'x' :* Nil))

testProd0, testProd1 :: NS (NP I) ExampleProd'
testProd0 = Z (I 5 :* I 13 :* I True :* Nil)
testProd1 = S (Z (I 5 :* I 'x' :* Nil))

data Tree' = BNode' Int Tree' Tree' | MNode' Char Tree' | Leaf'

type Test = ToContext 'F Tree' '[ '[Int, Tree', Tree'], '[]]

test :: NS (NP I) Test
test = Z (I Proxy :* I 5 :* I Hole :* I Leaf' :* Nil)

type Test' = '[Int, Tree'] .** ('[ '[]] .++ '[ '[]])

test' :: NS (NP I) Test'
test' = Z (I 5 :* I Leaf' :* Nil)

type Test'' = DiffProd Tree' '[Tree', Tree']

test'' :: NS (NP I) Test''
test'' = S (Z (I Leaf' :* I Hole :* Nil))

type Test''' = ToContext 'F Tree' '[ '[Int, Tree', Tree'], '[Char, Tree'], '[]]

test1 :: NS (NP I) Test'''
test1 = Z (I Proxy :* I 5 :* I Hole :* I Leaf' :* Nil)

test2 :: NS (NP I) Test'''
test2 = S (S (Z (I Proxy :* I 'a' :* I Hole :* Nil)))

type GTreeCtx' a b = ToContext 'F (Tree a b) (Code (Tree a b))

testTree1 :: NS (NP I) (GTreeCtx' Int Char)
testTree1 = Z (I Proxy :* I Hole :* I (Leaf 2) :* I 5 :* I 'b' :* I (Leaf 2) :* Nil)
testTree2 :: NS (NP I) (GTreeCtx' Int Char)
testTree2 = S (Z (I Proxy :* I (Leaf 2) :* I Hole :* I 5 :* I 'b' :* I (Leaf 2) :* Nil))
testTree3 :: NS (NP I) (GTreeCtx' Int Char)
testTree3 = S (S (Z (I Proxy :* I (Leaf 2) :* I (Leaf 2) :* I 5 :* I 'b' :* I Hole :* Nil)))
testTree4 :: NS (NP I) (GTreeCtx' Int Char)
testTree4 = S (S (S (Z (I Proxy :* I 'a' :* I Hole :* I (Leaf 2) :* Nil))))
testTree5 :: NS (NP I) (GTreeCtx' Int Char)
testTree5 = S (S (S (S (Z (I Proxy :* I 'a' :* I (Leaf 2) :* I Hole :* Nil)))))
