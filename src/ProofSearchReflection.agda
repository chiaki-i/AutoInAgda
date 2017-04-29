open import Data.List       as List               using ( List; []; _∷_; _∷ʳ_; map; length; filter; _++_; [_]
                                                        ; concat)
open import Data.Maybe      as Maybe              using (Maybe; just; nothing)
open import Data.Product    as Prod               using (_×_;_,_; proj₁; proj₂; ∃)
open import Data.Unit       as Unit               using (⊤)
open import Data.Nat        as Nat                using (ℕ; suc; zero; _+_)
open import Level                                 using (_⊔_)
open import Function                              using (id; const; _∘_; _$_)
open import Data.Vec        as Vec                using (Vec; _∷_; []; fromList)
open import Data.Bool
open import Relation.Nullary

open import Reflection
open import MinPrelude
open import MinPrelude.Reflection

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
      rname       : RuleName
      conclusion  : Term
      premises    : List (Arg Term)

  open Rule using (rname; conclusion; premises)

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

  mapArg : ∀ {A B : Set} → (A → B) → Arg A → Arg B
  mapArg f (arg i x) = arg i (f x)

  -- instantiate a Term with a given list of terms
  -- filling the variables.
  {-# TERMINATING #-}
  instₜ : List (Maybe Term) → Term → Term
  instₜ m (var x args) with join (lookup x m)
  -- TODO
  ... | p = var x []
  -- ... | just t  = t
  -- ... | nothing = var x args
  instₜ m (con c args) = con c (map (mapArg (instₜ m)) args )
  instₜ m (def f args) = def f (map (mapArg (instₜ m)) args )
  instₜ m (lam v (abs s x)) = lam v (abs s (instₜ m x))
  -- this case has to be work out
  instₜ m (pat-lam cs args) = pat-lam cs args
  instₜ m (pi a (abs s x))  = pi (mapArg (instₜ m) a) (abs s (instₜ m x))
  instₜ m (sort s)          = sort s
  instₜ m (lit l)           = lit l
  instₜ m (meta x args)     = meta x ((map (mapArg (instₜ m)) args ))
  instₜ m unknown           = unknown


  aux : List (Maybe Term) × List (Arg Term) → Arg Term → TC (List (Maybe Term) × List (Arg Term))
  aux (m , ips) arg′ with mapArg (instₜ m) arg′
  ... | iarg@(arg (arg-info visible r) x) = return ((nothing ∷ m) , ips ∷ʳ iarg)
  ... | iarg@(arg (arg-info _       r) x) = newMeta x >>= (λ t → return ((just t ∷ m) , ips ∷ʳ iarg))


  instᵣ : Rule → TC (List (Maybe Term) × Rule)
  instᵣ r = foldlM aux ([] , []) (premises r)
              >>= λ { (ms , prems) → return ( ms , rule (rname r)
                                                   (instₜ ms (conclusion r))
                                                   (filter visible? prems))}

  norm-rule : Rule → TC Rule
  norm-rule r = rule  (rname r) <$> normalise (conclusion r)
                                <*> mapM (traverse normalise) (premises r)

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
        solveAcc (suc k , g ∷ gs , p) di db = node di (mapM step (getHints db))
          where
            step : Hint → TC (SearchTree Proof DebugInfo)
            step h = catchTC (do g′ ← normalise g
                              -| ir ← instᵣ (getRule h)
                              -| unify′ g′ (conclusion (proj₂ ir))
                              ~| ir′ ← norm-rule (proj₂ ir)
                              -| return (solveAcc (prf ir′) (just (rname (getRule h)) )db))
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
    foldlM  (λ {( m , ( ys , zs )) x → caseM dfs′ k (m , suc n ∷ p) x of λ
                                            { (y , z) → return (suc m , (ys ∷ʳ y , zs ∷ʳ z)) }})
               (0 , ([] , []))
     >>= λ { ( _ , a , b) → return (concat a , (debug (suc n ∷ p) (suc k) false l) ∷ concat b) }

  dfs : Strategy
  dfs d s = dfs′ d (0 , []) s
