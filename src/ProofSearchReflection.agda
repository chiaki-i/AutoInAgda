open import Data.List as List
open import Reflection
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Unit
open import Data.Nat        as Nat                using (ℕ; suc; zero; _+_)
open import Level                                 using (_⊔_)
open import Function                              using (id; const; _∘_; _$_)
open import Data.Vec        as Vec                using (Vec; _∷_; []; fromList)
open import Data.TC.Extra
open import Data.Maybe.Extra
open import Data.List.Extra
open import Data.Bool
open import Relation.Nullary

module ProofSearchReflection
  (RuleName : Set )
  (unify′    : Term → Term → TC ⊤)
  where

  ----------------------------------------------------------------------------
  -- * define rules and utility functions                                 * --
  ----------------------------------------------------------------------------

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b ⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B

  -- introduce rules
  record Rule : Set where
    constructor rule
    field
      skolem?     : Bool
      rname       : RuleName
      conclusion  : Term
      premises    : List (Arg Term)

  open Rule using (skolem?; rname; conclusion; premises)

  -- alias for list of rules
  Rules : Set
  Rules = List Rule

  -- is an argument visible?
  visible? : ∀ {A : Set} → Arg A → Bool
  visible? (arg (arg-info visible _) _) = true
  visible? (arg (arg-info _′ _) _)      = false

  -- compute the arity of a rule, we discard any non-visible
  -- argument
  arity : (r : Rule) → ℕ
  arity = length ∘ premises


  ----------------------------------------------------------------------------
  -- * define hint databases                                              * --
  ----------------------------------------------------------------------------

  record IsHintDB : Set₁ where
    field
      HintDB   : Set
      Hint     : Set

    Hints : Set
    Hints = List Hint

    field
      getHints   : HintDB → Hints
      getRule    : Hint → Rule
      getTr      : Hint → (HintDB → HintDB)
      ε          : HintDB
      _∙_        : HintDB → HintDB → HintDB
      ret        : Rule → HintDB

    fromRules : Rules → HintDB
    fromRules []             = ε
    fromRules (r ∷ rs) = ret r ∙ fromRules rs

  newMetaArg : Arg Term → TC Term
  newMetaArg (arg i x) = newMeta x

  unArg : ∀ {A : Set} → Arg A → A
  unArg (arg i x) = x

  {-# TERMINATING #-}
  inst-term : List (Maybe Term) → Term → Maybe Term
  inst-term ms (var x args) with lookup ms x
  ... | nothing = nothing
  ... | just m  = m
  inst-term ms (con c args)  = con c <$-m> mapM-m (traverse-m-arg (inst-term ms))
                                           args
  inst-term ms (def c args)  = def c <$-m> mapM-m (traverse-m-arg (inst-term ms))
                                           args
  inst-term ms (lam v (abs s x)) = lam v <$-m> (abs s <$-m> inst-term ms x)
  inst-term ms (pat-lam _ _)     = nothing
  inst-term ms (pi a (abs s x))  = pi <$-m> (traverse-m-arg (inst-term ms)) a
                                      <*-m> (abs s <$-m> inst-term ms x)
  inst-term ms (sort s)    = just (sort s)
  inst-term ms (lit l)     = just (lit l)
  inst-term ms (meta x args) = meta x <$-m> mapM-m (traverse-m-arg (inst-term ms))
                                            args
  inst-term ms unknown = just unknown


  aux : List (Maybe Term) × List (Arg Term) → Arg Term → TC (List (Maybe Term) × List (Arg Term))
  aux (ms , ips) arg′ with traverse-m-arg (inst-term ms) arg′
  ... | nothing = typeError [ strErr "aux" ]
  ... | just iarg with iarg
  ... | (arg (arg-info v r) x) with v
  ... | visible = return ((nothing ∷ ms) , ips ∷ʳ iarg)
  ... | _       = newMetaArg iarg >>= (λ m → return (just m ∷ ms , ips ∷ʳ iarg))


  inst-rule : Rule → TC (List (Maybe Term) × Rule)
  inst-rule r with skolem? r
  ... | true  = return ([] , rule true
                              (rname r)
                              (conclusion r)
                              (filter visible? (premises r)))
  ... | false = foldlM-tc aux ([] , []) (premises r)
                >>= λ { (ms , prems) →
                maybe (λ ips → return ( ms , rule false (rname r)
                                      ips
                                      (filter visible? prems))) 
                      (typeError [ strErr "inst-rule" ])
                      (inst-term ms (conclusion r)) }

  norm-rule : Rule → TC Rule
  norm-rule r = rule (skolem? r) (rname r) <$-tc> normalise (conclusion r)
                                           <*-tc> mapM-tc (traverse-tc-arg normalise) (premises r)

  ----------------------------------------------------------------------------
  -- * define simple hint databases                                       * --
  ----------------------------------------------------------------------------

  simpleHintDB : IsHintDB
  simpleHintDB = record
      { HintDB   = Rules
      ; Hint     = Rule
      ; getHints = id
      ; getRule  = id
      ; getTr    = const id
      ; ε        = []
      ; _∙_      = _++_
      ; ret      = [_]
      }

  ----------------------------------------------------------------------------
  -- * define search trees, proofs and partial proofs                     * --
  ----------------------------------------------------------------------------

  -- simple alias to set apart the goal term
  Goal = Term

  -- search trees
  {-# NO_POSITIVITY_CHECK #-}
  data SearchTree (A B : Set) : Set where
    succ-leaf : B → A → SearchTree A B
    fail-leaf : B → SearchTree A B
    node      : B -> TC (List (SearchTree A B)) → SearchTree A B

  data Proof : Set where
     con : (name : RuleName) (args : List Proof) → Proof

  -- representation of an incomplete proof
  Proof′ : Set
  Proof′ = ∃[ k ] (Vec (Goal) k × (Vec Proof k → Proof))

  con′ : ∀ {k} (r : Rule) → Vec Proof (arity r + k) → Vec Proof (suc k)
  con′ {k} r xs = head ∷ rest
    where
      head : Proof
      head = con (rname r) (Vec.toList $ Vec.take (arity r) xs)
      rest : Vec Proof k
      rest = Vec.drop (arity r) xs

  DebugInfo = Maybe RuleName

  -- ----------------------------------------------------------------------------
  -- -- * define proof search function                                       * --
  -- ----------------------------------------------------------------------------

  module Extensible (isHintDB : IsHintDB) where

    open IsHintDB isHintDB

    {-# TERMINATING #-}
    solve : Term → HintDB → SearchTree Proof DebugInfo
    solve g db = solveAcc (1 , g ∷ [] , Vec.head) nothing db
      where
        solveAcc : Proof′ → DebugInfo → HintDB → SearchTree Proof DebugInfo
        solveAcc (0     ,     [] , p) di _  = succ-leaf di (p [])
        solveAcc (suc k , g ∷ gs , p) di db = node di (mapM-tc step (getHints db))
          where
            step : Hint → TC (SearchTree Proof DebugInfo)
            step h = catchTC (inst-rule (getRule h)
                              >>= λ ir → unify′ g (conclusion (proj₂ ir))
                              >>= λ _   → norm-rule (proj₂ ir)
                              >>= λ ir  → return (solveAcc (prf ir) (just (rname (getRule h)) )db))
                             (return (fail-leaf (just (rname (getRule h))) ))
              where
                prf : Rule → Proof′
                prf r = (length (premises r) + k) , prm′ , (p ∘ con′ r)
                  where
                    prm′ = Vec.map unArg (Vec.fromList (premises r))
                           Vec.++ gs


  ----------------------------------------------------------------------------
  -- * define various search strategies                                   * --
  ----------------------------------------------------------------------------

  -- debug information collected by the proof search
  record Debug (B : Set) : Set where
    constructor debug
    field
      index  : List ℕ
      depth  : ℕ
      fail?  : Bool
      info   : B

  Strategy : Set₁
  Strategy = ∀ {A B : Set} → (depth : ℕ) → SearchTree A B -> TC (List A × List (Debug B))

  dfs′ : ∀ {A B : Set} → (depth : ℕ) → (ℕ × List ℕ) → SearchTree A B -> TC (List A × List (Debug B))
  dfs′  zero   _  _                    = return ([] , [])
  dfs′ (suc k) (n , p) (fail-leaf l)   = return ([]    , [ debug (suc n ∷ p) (suc k) true l  ])
  dfs′ (suc k) (n , p) (succ-leaf l x) = return ([ x ] , [ debug (suc n ∷ p) (suc k) false l ])
  dfs′ (suc k) (n , p) (node l xs) = xs >>=
    foldlM-tc  (λ {( m , ( ys , zs )) x → caseM dfs′ k (m , suc n ∷ p) x of λ
                                            { (y , z) → return (suc m , (ys ∷ʳ y , zs ∷ʳ z)) }})
               (0 , ([] , []))
     >>= λ { ( _ , a , b) → return (concat a , (debug (suc n ∷ p) (suc k) false l) ∷ concat b) }

  dfs : Strategy
  dfs d s = dfs′ d (0 , []) s
