open import Builtin.Reflection
open import Prelude 
open import Container.Traversable
open import Tactic.Reflection.Equality

module Unification where

  private
    notUnify : ∀ {A : Set} → TC A
    notUnify = typeError []

    lift-unify : (Term → Term → TC ⊤) → Arg Term → Arg Term → TC ⊤
    lift-unify u (arg i x) (arg i₁ x₁) with i == i₁
    ... | yes _    = u x x₁
    ... | no _     = notUnify

  {-# TERMINATING #-}
  myunify : Term → Term → TC ⊤
  myunify t s with t | s
  myunify t s | (var x args) | (var x′ args′) with x == x′
  ... | yes _  =  sequenceA (zipWith (lift-unify myunify) args args′) >> return tt
  ... | _      = notUnify
  myunify t s | (con c args) | (con c′ args′) with c == c′
  ... | yes _  =  sequenceA (zipWith (lift-unify myunify) args args′) >> return tt
  ... | _      = notUnify
  myunify t s | con c args  | lit  l       = unify t s 
  myunify t s | lit l       | con c args   = unify t s 
  myunify t s | (def f args) | (def f′ args′) with f == f′
  ... | yes _  =  sequenceA (zipWith (lift-unify myunify) args args′) >> return tt
  ... | _      = notUnify
  myunify t s | lam v t₁ | lam v′ t′ = unify t s
  myunify t s | pi a b   | pi a′ b′  = unify t s
  myunify t s | agda-sort s₁  | agda-sort s₂ = unify t s
  myunify t s | lit l | lit l′     = unify t s
  myunify t s | meta m args | meta m′ args′ = unify t s
  myunify t s | var  m args | meta m′ args′ = unify t s
  myunify t s | meta m args | var  m′ args′ = unify t s 
  myunify t s | meta m args | lit  l        = unify t s 
  myunify t s | lit l       | meta m args   = unify t s 
  myunify t s | unknown | unknown = return tt
  myunify t s | _ | _ = notUnify
