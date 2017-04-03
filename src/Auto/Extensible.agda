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
                          renaming (unify to unifyTC)

open import Data.Maybe.Extra
open import Data.TC.Extra
open import Data.List.Extra

module Auto.Extensible (instHintDB : IsHintDB) where


open IsHintDB     instHintDB public
open PsExtensible instHintDB public
open Auto.Core               public using (dfs)

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
        showRuleName (var x ) = "var" ++ " " ++ showNat x

m-t : ∀ {A : Set} → Maybe (TC A) → TC (Maybe A)
m-t (just x) = just <$-tc> x
m-t nothing  = return nothing

-- auto
auto : Strategy → ℕ → HintDB → TelView → TC (String × Maybe Term)
auto search depth db tv
  with agda2goal×premises tv
... | (g , args) = caseM search (suc depth) (solve g (fromRules args ∙ db)) of λ
                     { ([] , d)    → return ((unlines ∘ map showDebug) d , nothing)
                     ; (p ∷ _ , d) → reify (length args) p >>= λ t → return ((unlines ∘ map showDebug) d , just t)}


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
