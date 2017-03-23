open import Auto.Core
open import Function      using (_∘_; _$_)
open import Data.List     using (_∷_; []; [_]; List; length; takeWhile; reverse; map; foldr; intersperse)
open import Data.Nat      using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Product  using (∃; _,_; _×_)
open import Data.Unit     using (⊤)
open import Data.String   using (String; _++_; toList; fromList; unlines)
open import Data.Char     using (_==_)
open import Data.Bool     using (Bool; true; false; not; if_then_else_)
open import Data.Maybe    using (Maybe; just; nothing; maybe′)
open import Reflection    using (Type; Term; Arg; Name; TC; quoteTC; getType; showName)
                          renaming (bindTC to _>>=_; returnTC to return; unify to unifyTC)


module Auto.Extensible (instHintDB : IsHintDB) where


open IsHintDB     instHintDB public renaming (return to returnHintDB)
open PsExtensible instHintDB public
open Auto.Core               public using (dfs; bfs)

private
  open Debug

  -- show debuging information
  showDebug : Debug (Maybe RuleName) → String
  showDebug d =
    maybe′  (λ rn → foldr _++_ "" ((foldr _++_ "" ∘ intersperse "." ∘ map showNat ∘ reverse $ (index d))
                                  ∷ " depth="  ∷ showNat (depth d)
                                  ∷ " " ∷ showRuleName rn
                                  ∷ " " ∷ [ if (fail? d) then "×" else "✓" ])) "" (info d)
      where
        showRuleName : RuleName → String
        showRuleName (name x) = fromList ∘ reverse ∘ takeWhile (not ∘ (_== '.'))
                                         ∘ reverse ∘ toList $ showName x
        showRuleName (var x)  = "var" ++ " " ++ showNat x


-- auto
auto : Strategy → ℕ → HintDB → Type → Ctx → Maybe (String × Maybe (TC Term))
auto search depth db type ctx
  with agda2goal×premises type
... | nothing = nothing
... | just ((n , g) , args)
  with context2premises (length args) ctx
... | nothing = nothing
... | just ctxs
  with search (suc depth) (solve g (fromRules ctxs ∙ (fromRules args ∙ db)))
... | ([] , d)    = just ((unlines ∘ map showDebug) d , nothing)
... | (p ∷ _ , d) = just ((unlines ∘ map showDebug) d , just (reify (length args) p))


-- HintDB
private
  mkHintDB : HintDB → Maybe (∃ Rule) → HintDB
  mkHintDB db nothing        = db
  mkHintDB db (just (_ , r)) = (returnHintDB r) ∙ db

infixl 5 _<<_

macro
  _<<_ : HintDB → Name → (Term → TC ⊤)
  db << nm = λ h   → getType nm
           >>= λ t → quoteTC (mkHintDB db (name2term nm t))
           >>= unifyTC h
