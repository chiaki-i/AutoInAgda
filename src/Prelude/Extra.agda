open import Prelude
open import Builtin.Reflection

-- a bunch of useful functions that are missing from prelude
module Prelude.Extra where

  foldlM : ∀ {A B : Set} → (B → A → TC B) → B → List A → TC B
  foldlM f b xs = foldl (λ tcb a → tcb >>= (λ b → f b a)) (return b) xs

  _∷ʳ_ : ∀ {A : Set} → List A → A → List A
  xs ∷ʳ x = xs ++ [ x ]

  takeVec : ∀ {A : Set} m {n} → Vec A (m + n) → Vec A m
  takeVec zero vs          = []
  takeVec (suc m) (x ∷ vs) = x ∷ takeVec m vs

  dropVec : ∀ {A : Set} m {n} → Vec A (m + n) → Vec A n
  dropVec zero vs          = vs
  dropVec (suc m) (x ∷ vs) = dropVec m vs

  headVec : ∀ {A : Set} {n} → Vec A (1 + n) → A
  headVec (x ∷ xs) = x
