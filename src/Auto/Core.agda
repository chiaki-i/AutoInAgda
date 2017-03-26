open import Function                   using (_∘_; id; flip)
open import Data.Nat     as Nat        using (ℕ; suc; zero; pred)
open import Data.List    as List       using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Product as Prod       using (_×_; _,_)
open import Data.Maybe   as Maybe      using (Maybe; just; nothing; maybe)
open import Data.Maybe.Extra           using (_<$-m>_)
open import Data.Bool                  using (true; false)
open import Reflection
open import Data.TC.Extra              using (return; _>>=_) 

module Auto.Core where

  -- define rule names for the proof terms/rules that our proof search will
  -- return/use; we'll use standard Agda names, together with rule-variables.
  data RuleName : Set where
    name  : Name → RuleName
    var   : ℕ    → RuleName

  -- -- now we can load the definitions from proof search
  open import ProofSearchReflection RuleName
    as PS public renaming (module Extensible to PsExtensible)


  -- return a view of a pi type
  telView : Type → List (Arg Type) × Type
  telView (pi a (abs _ b)) with telView b
  ... | (l , t) = a ∷ l , t
  telView a = [] , a

  -- convert an Agda name to a rule-term.
  name2term : Name → Type → Rule
  name2term nm t with telView t
  ... | prems , concl = rule false (name nm) concl prems

  -- convert an Agda term to a goal-term, together with a `HintDB`
  -- representing the premises of the rule---this means that for a
  -- term of the type `A → B` this function will generate a goal of
  -- type `B` and a premise of type `A`.
  agda2goal×premises : Type → Term × Rules
  agda2goal×premises t with telView t
  ... | prems , goal = goal , toPremises 0 prems
    where
      toPremises : ℕ → List (Arg Term) → Rules
      toPremises i [] = []
      toPremises i (arg _ t ∷ ts) = rule true (var i) t [] ∷ toPremises (pred i) ts

  -- A context is a deBruijn indexed list of the types of the variables.
  Ctx = List Type

  -- convert an Agda context to a `HintDB`.
  context2premises : (index : ℕ) → Ctx → Rules
  context2premises i []       = []
  context2premises i (t ∷ ts) with telView t
  ... | prems , goal = rule true (var i) goal prems ∷ context2premises (suc i) ts


  -- function which reifies untyped proof terms (from the
  -- `ProofSearch` module) to untyped Agda terms.
  mutual
    proof2AgTerm : Proof → TC Term
    proof2AgTerm (con (var i) ps)  = return (var i [])
    proof2AgTerm (con (name n) ps) =
      getDefinition n >>=
        λ { (function cs)       → children2AgTerms ps >>= (return ∘ def n)
          ; (constructor′ d)    → children2AgTerms ps >>= (return ∘ con n) 
          ; (data-type pars cs) → return unknown
          ; (record′ c)         → return unknown
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

  intros : ℕ → Term → Term
  intros  zero   t = t
  intros (suc k) t = lam visible (abs "_" ((intros k t)))

  reify : ℕ → Proof → TC Term
  reify n p = proof2AgTerm p >>= (return ∘ intros n)
