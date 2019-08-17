open import Function     using (const; id)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; name2rule)
open import Data.List    using ([]; [_]; _++_)
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Reflection   using (Name; Term; TC; inferType; getContext; quoteTC; unify) renaming (bindTC to _>>=_)

module Auto where

open import Auto.Extensible simpleHintDB public renaming (auto to auto′)

macro
  auto : ℕ → HintDB → Term → TC ⊤
  auto depth hintdb hole =
    inferType hole >>= λ type → getContext
                   >>= λ ctx → auto′ dfs depth hintdb type ctx
                   >>= unify hole

  {- If we replace the macro using runTacT above with the less specialized version runTac
     the example Example/Even is not able to compile (loops) -}
  -- auto depth hintdb = runTac (λ h → inferType h >>= (λ t → auto′ dfs depth hintdb t))
