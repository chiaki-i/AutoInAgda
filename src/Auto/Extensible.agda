open import Auto.Core
open import Prelude

module Auto.Extensible (instHintDB : IsHintDB) where


open IsHintDB     instHintDB public
open PsExtensible instHintDB public
open Auto.Core               public using (dfs)

private
  open Debug

  -- show debuging information
  showDebug : Debug (Maybe RuleName) → String
  showDebug d =
    maybe  (λ rn → foldr _++_ "" ((foldr _++_ "" ∘ intersperse "." ∘ map show ∘ reverse $ (index d))
                                  ∷ " depth="  ∷ showNat (depth d)
                                  ∷ " " ∷ showRuleName rn
                                  ∷ " " ∷ [ if (fail? d) then "×" else "✓" ])) "" (info d)
      where
        showRuleName : RuleName → String
        showRuleName (name x) = packString ∘ reverse ∘ takeWhile (not ∘ (_== '.'))
                                         ∘ reverse ∘ unpackString $ show x
        showRuleName (var x ) = "var" ++ " " ++ show x

-- auto
auto : Strategy → ℕ → HintDB → TelView × ℕ → TC (String × Maybe Term)
auto search depth db (tv , n)
  with agda2goal×premises tv
... | (g , args) = caseM search (suc depth) (solve g (fromRules args ∙ db)) of λ
                     { ([] , d)    → return ((unlines ∘ map showDebug) d , nothing)
                     ; (p ∷ _ , d) → reify n p >>= λ t → return ((unlines ∘ map showDebug) d , just t)}


-- HintDB
private
  mkHintDB : HintDB → Rule → HintDB
  mkHintDB db r = (ret r) ∙ db

infixl 5 _<<_

macro
  _<<_ : HintDB → Name → (Term → TC ⊤)
  db << nm = λ h   → getType nm
           >>= λ t → quoteTC (mkHintDB db (name2rule nm t))
           >>= unifyTC h
