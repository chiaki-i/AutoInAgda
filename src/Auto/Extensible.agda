open import Auto.Core
open import Prelude
open import Prelude.Extra
open import Tactic.Reflection
open import Builtin.Reflection

module Auto.Extensible (instHintDB : IsHintDB) where

  open IsHintDB     instHintDB public
  open PsExtensible instHintDB public
  open Auto.Core               public using (dfs)

  private
    open Debug

    showRuleName : RuleName → String
    showRuleName (name x) = packString ∘ reverse ∘ takeWhile isAlphaNum
                                       ∘ reverse ∘ unpackString $ show x
    showRuleName (var x ) = "var" <> " " <> show x

    -- show debuging information
    showDebug : Debug (Maybe RuleName) → String
    showDebug d = "Hahah"
      -- maybe  (λ rn → foldr <> "" ((intersperse "." ∘ map show ∘ reverse $ (index d))
      --                               ∷ " depth="  ∷ show (depth d)
      --                               ∷ " " ∷ showRuleName rn
      --                               ∷ " " ∷ [ if (fail? d) then "×" else "✓" ])) "" (info d)

  -- auto
  auto : Strategy → Nat → HintDB → TelView × Nat → TC (String × Maybe Term)
  auto search depth db (tv , n)
    with agda2goal×premises tv
  ... | (g , args) = caseM search (suc depth) (solve g (fromRules args ∙ db)) of λ
                      { ([] , d)    → return ("Bad" , nothing)
                      ; (p ∷ _ , d) → reify n p >>= λ t → return ("Good " , just t)}


  private

    -- add a hint to the database.
    add-hint : HintDB → Name → TC HintDB
    add-hint db nm =  do t ← getType nm
                   -| return ( ret (name2rule nm t) ∙ db)

    -- make a database with all the constructors.
    add-constr : Name → TC HintDB
    add-constr nm = caseM getDefinition nm of λ
                     { (data-type pars cs) → foldlM add-hint ε cs
                     ; _                   → typeError [ strErr "Non datatype when crafting HintDB" ]}

  infixl 5 _<<_

  macro
    _<<_ : HintDB → Name → Tactic
    db << nm = evalTC (add-hint db nm)

    constructors : Name → Tactic
    constructors = evalTC ∘′ add-constr
