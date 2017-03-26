open import Data.Maybe  using (Maybe; just; nothing)
open import Data.List   using (List; _∷_; [])
open import Reflection  using (Arg; arg)

module Data.Maybe.Extra where

_<$-m>_ : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
f <$-m> just x  = just (f x)
f <$-m> nothing = nothing

mapM-m : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
mapM-m f [] = just []
mapM-m f (x ∷ xs) with f x | mapM-m f xs
... | just x′ | just xs′ = just (x′ ∷ xs′)
... | _       | _        = nothing

_<*-m>_ : ∀ {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
just f <*-m> just x = just (f x)
_ <*-m> _           = nothing

infixl 4 _<$-m>_
infixl 4 _<*-m>_

traverse-m-arg : ∀ {A B : Set} → (A → Maybe B) → Arg A → Maybe (Arg B)
traverse-m-arg f (arg i x) with f x
... | just x′ = just (arg i x′)
... | nothing = nothing
