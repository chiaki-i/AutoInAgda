open import Data.List       as List               using ( List; []; _∷_; _∷ʳ_; map; length; filter; _++_; [_]
                                                        ; concat; foldr)
open import Coinduction
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
open import Steroids
open import Steroids.Reflection

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

  -- rules are composed of a list of premises and a conclusion
  -- each premise is marked with its visibility so the rule can
  -- be properly instantiated.
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

  -- instantiate a Term with a given list of terms
  -- (all the terms in the list should be metavariables)
  -- filling the variables.
  {-# TERMINATING #-}
  instₜ : List (Maybe Term) → Term → Term
  instₜ m (var x args) with lookup x m
  instₜ m (var x args) | just (just x₁) = x₁
  instₜ m (var x args) | just nothing   = var x args
  instₜ m (var x args) | nothing        = var x args
  instₜ m (con c args) = con c (map (fmap (instₜ m)) args )
  instₜ m (def f args) = def f (map (fmap (instₜ m)) args )
  instₜ m (lam v (abs s x)) = lam v (abs s (instₜ m x))
  instₜ m (pi a (abs s x))  = pi (fmap (instₜ m) a) (abs s (instₜ m x))
  instₜ m (sort s)          = sort s
  instₜ m (lit l)           = lit l
  instₜ m (meta x args)     = meta x ((map (fmap (instₜ m)) args ))
  instₜ m unknown           = unknown
  -- this case hasn't been studied
  instₜ m (pat-lam cs args) = pat-lam cs args


  -- instantiate a Rule returning the Rule with all the locally
  -- bound variables replaced by fresh metavariables.
  -- it also returns the list of this metavariables for debugging purposes
  instᵣ : Rule → TC (List (Maybe Term) × Rule)
  instᵣ r = foldlM aux ([] , []) (premises r)
              >>= λ { (ms , prems) → return ( ms , rule (rname r)
                                                        (instₜ ms (conclusion r))
                                                        (filter visible? prems))}
     where
        aux : List (Maybe Term) × List (Arg Term) → Arg Term → TC (List (Maybe Term) × List (Arg Term))
        aux (m , ips) arg′ with fmap (instₜ m) arg′
        ... | iarg@(arg (arg-info visible r) x) = return ((nothing ∷ m) , ips ∷ʳ iarg)
        ... | iarg@(arg (arg-info _       r) x) = newMeta x >>= (λ t → return ((just t ∷ m) , ips ∷ʳ iarg))

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

  -- -------------------------------------------------------------------------
  -- * define search trees, proofs and partial proofs                     * --
  ----------------------------------------------------------------------------

  Goal = Term

  -- search tree
  -- NO_POSITIVITY_CHECK is required due to the use of the TC monad in the node
  -- constructor.
  {-# NO_POSITIVITY_CHECK #-}
  data SearchTree (A B : Set) : Set where
    succ-leaf : B → A → SearchTree A B
    fail-leaf : B → SearchTree A B
    node      : B → List (TC (SearchTree A B)) → SearchTree A B

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

  DebugInfo = Maybe RuleName × Maybe Term

  -- ----------------------------------------------------------------------------
  -- -- * define proof search function                                       * --
  -- ----------------------------------------------------------------------------

  module Extensible (isHintDB : IsHintDB) where

    open IsHintDB isHintDB

    {-# TERMINATING #-}
    solve : Term → HintDB → SearchTree Proof DebugInfo
    solve g db = solveAcc (1 , g ∷ [] , Vec.head) (nothing , nothing) db
      where
        solveAcc : Proof′ → DebugInfo → HintDB → SearchTree Proof DebugInfo
        solveAcc (0     ,     [] , p) di _  = succ-leaf di (p [])
        solveAcc (suc k , g ∷ gs , p) di db = node di (map step (getHints db))
          where
            step : Hint → TC (SearchTree Proof DebugInfo)
            step h = catchTC (do g′  ← normalise g
                              -| ir  ← instᵣ (getRule h)
                              -| unify′ g′ (conclusion (proj₂ ir))
                              ~| return (solveAcc (prf (proj₂ ir)) (just (rname (getRule h)) , nothing ) db))
                             (return (fail-leaf (just (rname (getRule h)) , just g) ))
              where
                prf : Rule → Proof′
                prf r = (length (premises r) + k) , prm′ , (p ∘ con′ r)
                  where
                    prm′ = Vec.map unArg (Vec.fromList (premises r))
                           Vec.++ gs


  -- ----------------------------------------------------------------------------
  -- -- * proof search
  -- ----------------------------------------------------------------------------

  -- debug information collected by the proof search
  -- + the index indicates the location as branch in the proof tree
  -- + the depth of the node
  -- + the fail? whether is a failed node or not (depth has been reached)
  -- + the debugging information itself
  record Debug (B : Set) : Set where
    constructor debug
    field
      index  : List ℕ
      depth  : ℕ
      fail?  : Bool
      info   : B

  -- strategy now takes into account not only the result but also the debugging information.
  -- such information holds the trace of the search through the proof tree.
  Strategy : Set₁
  Strategy = ∀ {A B : Set} → (depth : ℕ) → SearchTree A B -> TC (Maybe A × List (Debug B))

  private
    -- utility function
    mapSecond : ∀ {A B C : Set} → (B → C) → A × B → A × C
    mapSecond f (fst , snd) = fst , f snd

  -- workhorse function for depth-first search
  -- due to the use of TC monad bind (>>=) we need to use the TERMINATING flag.
  {-# TERMINATING #-}
  mutual
    dfs′ : ∀ {A B : Set} → (depth : ℕ) → (ℕ × List ℕ) → SearchTree A B -> TC (Maybe A × List (Debug B))
    dfs′  zero   _  _                    = return (nothing , [])
    dfs′ (suc k) (n , p) (fail-leaf l)   = return (nothing , [ debug (suc n ∷ p) (suc k) true l  ])
    dfs′ (suc k) (n , p) (succ-leaf l x) = return (just x  , [ debug (suc n ∷ p) (suc k) false l ])
    dfs′ (suc k) (n , p) (node l xs)     = mapSecond (debug (suc n ∷ p) (suc k) false l ∷_) <$> dfs′′ 0 l xs k (n , p)

    dfs′′ : ∀ {A B : Set} → ℕ → B → List (TC (SearchTree A B)) → ℕ → (ℕ × List ℕ) → TC (Maybe A × List (Debug B))
    dfs′′ i l [] k (n , p)       = return (nothing ,  [])
    dfs′′ i l (x ∷ xs) k (n , p) = x >>= λ x′ →  caseM dfs′ k (i , suc n ∷ p) x′ of λ
                                                { (just x  , db) → return (just x , db )
                                                ; (nothing , db) →  mapSecond (db ++_) <$> dfs′′ (i + 1) l xs (suc k) (n , p)}

  -- depth-first search strategy
  dfs : Strategy
  dfs d s = dfs′ d (0 , []) s
