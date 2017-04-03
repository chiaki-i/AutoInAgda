open import Unification
open import Context
open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Telescope

module Auto.Core where


  open import Context public

  -- define rule names for the proof terms/rules that our proof search will
  -- return/use; we'll use standard Agda names, together with rule-variables.
  data RuleName : Set where
    name  : Name → RuleName
    var   : Nat  → RuleName

  -- -- now we can load the definitions from proof search
  open import ProofSearchReflection RuleName myunify
    as PS public renaming (module Extensible to PsExtensible)

  -- convert an Agda name to a rule-term.
  name2rule : Name → Type → Rule
  name2rule nm t with telView t
  ... | (prems , concl) = rule false (name nm) concl prems

  -- convert an Agda term to a goal-term, together with a `HintDB`
  -- representing the premises of the rule---this means that for a
  -- term of the type `A → B` this function will generate a goal of
  -- type `B` and a premise of type `A`.
  -- in case the argument is not visible we just ignore it.
  agda2goal×premises : TelView → Term × Rules
  agda2goal×premises (prems , goal) = goal , toPremises 0 (reverse prems)
    where
      toPremises : Nat → List (Arg Term) → Rules
      toPremises i [] = []
      toPremises i (arg (arg-info visible r) t ∷ ts) = rule true (var i) t [] ∷ toPremises (suc i) ts
      toPremises i (arg (arg-info _′      r) _ ∷ ts) = toPremises (suc i) ts


  -- function which reifies untyped proof terms (from the
  -- `ProofSearch` module) to untyped Agda terms.
  mutual
    proof2AgTerm : Proof → TC Term
    proof2AgTerm (con (var i) ps)  = return (var i [])
    proof2AgTerm (con (name n) ps) =
      getDefinition n >>=
        λ { (function cs)       → children2AgTerms ps >>= (return ∘ def n)
          -- ; (constructor′ d)    → children2AgTerms ps >>= (return ∘ con n) 
          ; (data-type pars cs) → return unknown
          -- ; (record′ c)         → return unknown
          ; axiom               → return unknown
          ; primitive′          → return unknown }

    children2AgTerms : List Proof → TC (List (Arg Term))
    children2AgTerms []       = return []
    children2AgTerms (p ∷ ps) = proof2AgTerm p
                              >>= λ r  → children2AgTerms ps
                              >>= λ cs → return (toArg r ∷ cs)
      where
        toArg : Term → Arg Term
        toArg = arg (arg-info visible relevant)

  intros : Nat → Term → Term
  intros  zero   t = t
  intros (suc k) t = lam visible (Abs.abs "_" ((intros k t)))

  reify : Nat → Proof → TC Term
  reify n p = proof2AgTerm p >>= (return ∘ intros n)
