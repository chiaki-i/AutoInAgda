open import Data.List  using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat   using (ℕ; suc; zero)

module Data.List.Extra where

lookup : ∀ {A : Set} → List A → ℕ → Maybe A
lookup [] z = nothing
lookup (x ∷ _)  zero    = just x
lookup (x ∷ xs) (suc z) = lookup xs z

safe-head : ∀ {A : Set} → List A → Maybe A
safe-head []      = nothing
safe-head (x ∷ _) = just x
