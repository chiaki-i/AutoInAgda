open import Auto.Core
open import Function     using (_∘_; const)
open import Data.List    using (_∷_; []; List; length)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (∃; _,_; Σ)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Reflection   using (Type; Term; Arg; Name; lam; abs; visible; TC; quoteTC; getType; normalise) renaming (bindTC to _>>=_; returnTC to return)

module Auto.Extensible (instHintDB : IsHintDB) where


open IsHintDB     instHintDB public renaming (return to returnHintDB)
open PsExtensible instHintDB public
open Auto.Core               public using (dfs; bfs; Exception; throw; searchSpaceExhausted; unsupportedSyntax)


auto : Strategy → ℕ → HintDB → Type → List (Arg Type) → TC Term
auto search depth db type ctx
  with context2premises ctx
... | inj₁ msg₁ = return (quoteError msg₁)
... | inj₂ ctxs
  with agda2goal×premises (length ctxs) type
... | inj₁ msg  = return (quoteError msg)
... | inj₂ ((n , g) , args)
  with search (suc depth) (solve g (fromRules ctxs ∙ (fromRules args ∙ db)))
... | []      = return (quoteError searchSpaceExhausted)
... | (p ∷ _) = reify p >>= (return ∘ intros)
  where
    intros : Term → Term
    intros = introsAcc (length args)
      where
        introsAcc : ℕ → Term → Term
        introsAcc  zero   t = t
        introsAcc (suc k) t = lam visible (abs "dummy" ((introsAcc k t)))



infixl 5 _<<_


_<<_ : HintDB → Error (∃ Rule) → HintDB
db << inj₁ _ = db
db << inj₂ (_ , r) = (returnHintDB r) ∙ db


runTC : ∀ {a} {A : Set a} → TC A → Term → TC ⊤
runTC tc h = tc >>= (λ r → quoteTC r >>= (λ t → Reflection.unify h t))

macro
  q : Name → Term → TC ⊤
  q nm = runTC (name2rule nm)

