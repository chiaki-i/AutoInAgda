open import Function     using (_∘_; const; id)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; name2rule)
open import Data.List    using (_∷_; List; length; []; [_]; _++_)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Reflection   using (Name; Type; Arg; Term; TC;
                                inferType; getContext; getDefinition; getType; normalise;
                                quoteTC;
                                typeError; strErr; termErr;
                                unify)
                         renaming (bindTC to _>>=_; returnTC to return)
open import Auto.Core
open import Auto.Extensible simpleHintDB public renaming (auto to auto′)

module Auto.Debug where

auto-showStrategy : Strategy → ℕ → HintDB → Type → List (Arg Type) → TC Term
auto-showStrategy search depth db type ctx
  with context2premises ctx
... | inj₁ msg₁ = return (quoteError msg₁)
... | inj₂ ctxs
  with agda2goal×premises (length ctxs) type
... | inj₁ msg  = return (quoteError msg)
... | inj₂ ((n , g) , args)
  with (search (suc depth) (solve g (fromRules ctxs ∙ (fromRules args ∙ db))))
... | term = quoteTC term >>= normalise

auto-showSolve : Strategy → ℕ → HintDB → Type → List (Arg Type) → TC Term
auto-showSolve search depth db type ctx
  with context2premises ctx
... | inj₁ msg₁ = return (quoteError msg₁)
... | inj₂ ctxs
  with agda2goal×premises (length ctxs) type
... | inj₁ msg  = return (quoteError msg)
... | inj₂ ((n , g) , args)
  with (solve g (fromRules ctxs ∙ (fromRules args ∙ db)))
... | term = quoteTC term >>= normalise

debugMessage : Term → TC Term
debugMessage term = typeError ((strErr "!Debug Mode! \n") ∷ (termErr term) ∷ [])

macro
  -- show the current context captured by Reflection.getContext
  debugContext : Term → TC ⊤
  debugContext hole =
    inferType hole >>= λ type → getContext
                   >>= λ ctx → quoteTC ctx
                   >>= λ term → debugMessage term
                   >>= Reflection.unify hole
  -- `unify` does not have any real meanings, it's just because macros should return `TC ⊤`.

  -- show the type of the current hole (= goal), but the hole has little info (e.g. only showing a metavariable like _74)
  debugGoal : Term → TC ⊤
  debugGoal hole =
    debugMessage hole >>= Reflection.unify hole

  -- show the result of the dfs/bfs function
  -- the result has type `List Proof`
  debugStrategy : ℕ → HintDB → Term → TC ⊤
  debugStrategy depth hintdb hole =
    inferType hole >>= λ type → getContext
                   >>= λ ctx → auto-showStrategy Auto.Core.dfs depth hintdb type ctx
                   >>= λ term → debugMessage term
                   >>= Reflection.unify hole

  -- show the result of `solve` function
  -- the result has type `SearchTree Proof`
  debugSolve : ℕ → HintDB → Term → TC ⊤
  debugSolve depth hintdb hole =
    inferType hole >>= λ type → getContext
                   >>= λ ctx → auto-showSolve Auto.Core.dfs depth hintdb type ctx
                   >>= λ term → debugMessage term
                   >>= Reflection.unify hole
