open import Reflection       renaming (unify to unifyTC)
open import Data.Nat         renaming (_≟_ to _ℕ≟_)
open import Relation.Nullary using    (yes; no)
open import Data.Unit        using    (⊤; tt)
open import Data.List        using    (List; []; _∷_; zipWith)

open import Steroids
open import Steroids.Reflection

module Unification where

  -- throw an error
  notUnify : ∀ {A : Set} → TC A
  notUnify = typeError []

  -- lift unification to work on Arg
  lift-unify : (Term → Term → TC ⊤) → Arg Term → Arg Term → TC ⊤
  lift-unify u (arg i x) (arg i₁ x₁) with i ≟-Arg-info i₁
  ... | yes _    = u x x₁
  ... | no _     = notUnify

  -- example unification function. the interesting case is the constructor
  -- def that unifies one by one the arguments of it.
  {-# TERMINATING #-}
  unify : Term → Term → TC ⊤
  unify t s with t | s
  unify t s | (var x args) | (var x′ args′) with x ℕ≟ x′
  ... | yes _  =  sequence (zipWith (lift-unify unify) args args′) >> return tt
  ... | _      = notUnify
  unify t s | (con c args) | (con c′ args′) with c ≟-Name c′
  ... | yes _  =  sequence (zipWith (lift-unify unify) args args′) >> return tt
  ... | _      =  notUnify
  unify t s | con c args   | lit  l       = unifyTC t s
  unify t s | con c args   | meta m args′ = unifyTC t s
  unify t s | meta m args  | con c args′ = unifyTC t s
  unify t s | lit l       | con c args   = unifyTC t s
  unify t s | (def f args) | (def f′ args′) with f ≟-Name f′
  ... | yes _  =  sequence (zipWith (lift-unify unify) args args′) >> return tt
  ... | _      = notUnify
  unify t s | lam v t₁ | lam v′ t′ = unifyTC t s
  unify t s | pi a b   | pi a′ b′  = unifyTC t s
  unify t s | sort s₁  | sort s₂   = unifyTC t s
  unify t s | lit l | lit l′       = unifyTC t s
  unify t s | meta m args | meta m′ args′ with m ≟-Meta m′
  ... | yes _  =  sequence (zipWith (lift-unify unify) args args′) >> return tt
  ... | _      = notUnify
  unify t s | var  m args | meta m′ args′ = unifyTC t s
  unify t s | meta m args | var  m′ args′ = unifyTC t s
  unify t s | meta m args | lit  l        = unifyTC t s
  unify t s | lit l       | meta m args   = unifyTC t s
  unify t s | unknown | unknown = return tt
  unify t s | _ | _ = notUnify
