open import Data.Maybe  using (Maybe; just; nothing)

module Data.Maybe.Extra where

_<$>_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Maybe A → Maybe B
f <$> nothing = nothing
f <$> just y  = just (f y)
