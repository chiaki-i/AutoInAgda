module Reflection.Tactic where

open import Reflection renaming (returnTC to return; bindTC to _>>=_)
open import Data.Unit  using (⊤)

Tactic : ∀ {α} → Set α → Set α
Tactic A = Term → TC A

Macro = Tactic ⊤

runTac : ∀ {a} {A : Set a} → Tactic A → Macro
runTac tc h = tc h >>= (λ r → quoteTC r >>= (λ t → unify h t))

-- Specialized version of runTac where the 'tactic' already returns
-- a Term
runTacT : Tactic Term → Macro
runTacT  tc h = tc h >>= unify h

runTC : ∀ {a} {A : Set a} → TC A → Macro
runTC tc h = tc >>= (λ r → quoteTC r >>= (λ t → unify h t))

