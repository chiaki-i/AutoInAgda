open import Reflection
open import Data.Nat as Nat
open import Relation.Nullary
open import Data.Unit
open import Data.List using (List; []; _∷_; zipWith)

open import Steroids
open import Steroids.Reflection

module Unification where

notUnify : ∀ {A : Set} → TC A
notUnify = typeError []

lift-unify : (Term → Term → TC ⊤) → Arg Term → Arg Term → TC ⊤
lift-unify u (arg i x) (arg i₁ x₁) with i ≟-Arg-info i₁
... | yes _    = u x x₁
... | no _     = notUnify


{-# TERMINATING #-}
myunify : Term → Term → TC ⊤
myunify t s with t | s
myunify t s | (var x args) | (var x′ args′) with x Nat.≟ x′
... | yes _  =  sequence (zipWith (lift-unify myunify) args args′) >> return tt
... | _      = notUnify
myunify t s | (con c args) | (con c′ args′) with c ≟-Name c′
... | yes _  =  sequence (zipWith (lift-unify myunify) args args′) >> return tt
... | _      =  notUnify
myunify t s | con c args   | lit  l       = unify t s
myunify t s | con c args   | meta m args′ = unify t s
myunify t s | meta m args  | con c args′ = unify t s
myunify t s | lit l       | con c args   = unify t s
myunify t s | (def f args) | (def f′ args′) with f ≟-Name f′
... | yes _  =  sequence (zipWith (lift-unify myunify) args args′) >> return tt
... | _      = notUnify
myunify t s | lam v t₁ | lam v′ t′ = unify t s
myunify t s | pi a b   | pi a′ b′  = unify t s
myunify t s | sort s₁  | sort s₂ = unify t s
myunify t s | lit l | lit l′     = unify t s
myunify t s | meta m args | meta m′ args′ with m ≟-Meta m′
... | yes _  =  sequence (zipWith (lift-unify myunify) args args′) >> return tt
... | _      = notUnify
myunify t s | var  m args | meta m′ args′ = unify t s
myunify t s | meta m args | var  m′ args′ = unify t s
myunify t s | meta m args | lit  l        = unify t s
myunify t s | lit l       | meta m args   = unify t s
myunify t s | unknown | unknown = return tt
myunify t s | _ | _ = notUnify
