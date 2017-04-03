open import Reflection  using (TC; bindTC; returnTC; Arg; arg)
open import Function    using (_∘_; case_of_)
open import Data.List   using (List; _∷_; []; foldl)

module Data.TC.Extra where

_>>=_  = bindTC
infixl 5 _>>=_

_>>_ : ∀ {A B : Set} → TC A → TC B → TC B
m >> m₁ = m >>= λ _ → m₁

return = returnTC

_<$-tc>_ : ∀ {A B : Set} → (A → B) → TC A → TC B
f <$-tc> x  = x >>= return ∘ f

_<*-tc>_ : ∀ {A B : Set} → TC (A → B) → TC A → TC B
f <*-tc> x  = f >>= λ f → f <$-tc> x

infixl 4 _<$-tc>_
infixl 4 _<*-tc>_

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


infix -10 do_
do_ : ∀ {a} {A : Set a} → A → A
do x = x

infixr 0 do-bind do-seq do-let

syntax do-bind  m (λ x → m₁) = x ← m -| m₁
syntax do-seq   m m₁         = m ~| m₁
syntax do-let   m (λ x → m₁) = x := m -| m₁

do-bind = _>>=_
do-seq = _>>_
do-let = case_of_

infixr 0 caseM_of_
caseM_of_ = _>>=_
