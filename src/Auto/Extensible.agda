open import Auto.Core
open import Function      using (_∘_; _$_; case_of_)
open import Data.List     using (_∷_; []; [_]; List; length; takeWhile; reverse; map; foldr; intersperse)
open import Data.Nat      using (ℕ; zero; suc; pred; _+_)
open import Data.Product  using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Unit     using (⊤)
open import Data.String   using (String; _++_; toList; fromList; unlines)
open import Data.Char     using (_==_)
open import Data.Bool     using (Bool; true; false; not; if_then_else_)
open import Data.Maybe    using (Maybe; just; nothing; maybe′)

open import Reflection
open import Steroids
open import Steroids.Reflection

module Auto.Extensible (instHintDB : IsHintDB) where

  open IsHintDB     instHintDB public
  open PsExtensible instHintDB public
  open Auto.Core               public using (dfs)

  private
    open Debug

    -- show debuging information
    showDebug : Debug (Maybe RuleName × Maybe Term) → String
    showDebug d =
      maybe′  (λ rn → foldr _++_ "" ((foldr _++_ "" ∘ intersperse "." ∘ map show′ ∘ reverse $ (index d))
                                    ∷ " depth="  ∷ show′ (depth d)
                                    ∷ " " ∷ showRuleName rn
                                    ∷ " " ∷ [ if (fail? d) then "×" else "✓" ])) "" (proj₁ (info d))
      ++ " "
      ++
      maybe′ (show′) "" (proj₂ (info d))
        where
          showRuleName : RuleName → String
          showRuleName (name x) = fromList ∘ reverse ∘ takeWhile (not ∘ (_== '.'))
                                          ∘ reverse ∘ toList $ showName x
          showRuleName (var x ) = "var" ++ " " ++ show′ x

  -- auto
  auto : Strategy → ℕ → HintDB → TelView × ℕ → TC (String × Maybe Term)
  auto search depth db (tv , n)
    with agda2goal×premises tv
  ... | (g , args) = caseM search (suc depth) (solve g (fromRules args ∙ db))  of λ
                         { (nothing , d)    → return ((unlines ∘ map showDebug) d , nothing)
                         ; (just p  , d) → reify n p >>= λ t → return ((unlines ∘ map showDebug) d , just t)}


  -- print the hint database
  printDB : HintDB → TelView × ℕ → Term → TC (String × Maybe Term)
  printDB db (tv , n) h
    with agda2goal×premises tv
  ... | (g , args) = quoteTC (fromRules args ∙ db) >>= λ t → typeError [ termErr t ]


  -- HintDB

  private

    -- add a new hint to the HintDB
    add-hint : HintDB → Name → TC HintDB
    add-hint db nm = do t ← getType nm
                    -| return (ret (name2rule nm t) ∙ db)

    -- given the name of a data-type, create a HintDB with
    -- all its constructors
    add-constr : Name → TC HintDB
    add-constr nm =
      caseM getDefinition nm of λ
        { (data-type pars cs) → foldlM add-hint ε cs
        ; _                   → typeError (strErr ("Non data-type name: " ++ showName nm) ∷ []) }


  macro
    _<<_ : HintDB → Name → Term → TC ⊤
    db << nm = λ h → add-hint db nm >>= quoteTC >>= unify h

    constructors : Name → Term → TC ⊤
    constructors nm = λ h → add-constr nm >>= quoteTC >>= unify h

  infixl 5 _<<_
