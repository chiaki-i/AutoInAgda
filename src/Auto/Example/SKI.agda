open import Auto

module Auto.Example.SKI where

I : ∀ {A : Set} → A → A
I = apply (auto 5 ε)

K : ∀ {A B : Set} → A → B → A
K = apply (auto 5 ε)

S : ∀ {A B C : Set} → (A → B → C) → (A → B) → A → C
S x y z = apply (auto 5 ε)
