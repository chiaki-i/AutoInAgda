open import Function     using (const; id)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule)
open import Data.List    using ([]; [_]; _++_)
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Reflection   using (Name; Term; TC; inferType; getContext; quoteTC; unify) renaming (bindTC to _>>=_)
open import Reflection.Tactic using (runTac; runTacT)

module Auto where

open import Auto.Extensible simpleHintDB public renaming (auto to auto′)

macro
  auto : ℕ → HintDB → Term → TC ⊤
  auto depth hintdb = runTacT (λ h → inferType h >>= (λ t → getContext >>= (λ ctx → auto′ dfs depth hintdb t ctx)))

  {- If we replace the macro using runTacT above with the less specialized version runTac
     the example Example/Even is not able to compile (loops) -}
  -- auto depth hintdb = runTac (λ h → inferType h >>= (λ t → auto′ dfs depth hintdb t))
