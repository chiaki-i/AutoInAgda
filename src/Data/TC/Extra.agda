open import Reflection  using (TC; bindTC; returnTC; Arg; arg)
open import Function    using (_∘_)
open import Data.List   using (List; _∷_; []; foldl)

module Data.TC.Extra where

_>>=_  = bindTC
infixl 5 _>>=_

return = returnTC

_<$-tc>_ : ∀ {A B : Set} → (A → B) → TC A → TC B
f <$-tc> x  = x >>= return ∘ f

foldlM-tc : ∀ {A B : Set} → (B → A → TC B) → B → List A → TC B
foldlM-tc f b xs = foldl (λ tcb a → tcb >>= (λ b → f b a)) (return b) xs

mapM-tc : ∀ {A B : Set} → (A → TC B) → List A → TC (List B)
mapM-tc f [] = return []
mapM-tc f (x ∷ xs) = f x >>= (λ x′ → mapM-tc f xs >>= (λ xs′ → return (x′ ∷ xs′)))

traverse-tc-arg : ∀ {A B : Set} → (A → TC B) → Arg A → TC (Arg B)
traverse-tc-arg f (arg i x) = f x >>= return ∘ arg i

sequence-tc : ∀ {A : Set} → List (TC A) → TC (List A)
sequence-tc []       = return []
sequence-tc (x ∷ xs) = x >>= λ x′ → sequence-tc xs >>= λ xs′ → return (x′ ∷ xs′)
