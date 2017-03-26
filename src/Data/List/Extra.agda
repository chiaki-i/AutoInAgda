open import Data.List  using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat   using (ℕ; suc; zero)

module Data.List.Extra where

index : ∀ {A : Set} → List A → ℕ → Maybe A
index [] z = nothing
index (x ∷ _)  zero    = just x
index (x ∷ xs) (suc z) = index xs z

safe-head : ∀ {A : Set} → List A → Maybe A
safe-head []      = nothing
safe-head (x ∷ _) = just x
