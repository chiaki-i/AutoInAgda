open import Prelude
open import Builtin.Reflection
open import Container.Traversable

module ProofSearchReflection
  (RuleName  : Set )
  (unify′    : Term → Term → TC ⊤)
  where

  _∷ʳ_ : ∀ {A : Set} → List A → A → List A
  xs ∷ʳ x = xs ++ [ x ]
  ----------------------------------------------------------------------------
  -- * define rules and utility functions                                 * --
  ----------------------------------------------------------------------------

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
  arity : (r : Rule) → Nat
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

  {-# TERMINATING #-}
  inst-term : List (Maybe Term) → Term → Maybe Term
  inst-term ms (var x args) with index ms x
  ... | nothing = nothing
  ... | just m  = m
  inst-term ms (con c args)  = con c <$> mapM (traverse (inst-term ms))
                                         args
  inst-term ms (def c args)  = def c <$> mapM (traverse (inst-term ms))
                                         args
  inst-term ms (lam v (abs s x)) = lam v <$> (Abs.abs s <$> inst-term ms x)
  inst-term ms (pat-lam _ _)     = nothing
  inst-term ms (pi a (abs s x))  = pi <$> (traverse (inst-term ms)) a
                                      <*> (Abs.abs s <$> inst-term ms x)
  inst-term ms (agda-sort s)    = just (agda-sort s)
  inst-term ms (lit l)     = just (lit l)
  inst-term ms (meta x args) = meta x <$> mapM (traverse (inst-term ms))
                                          args
  inst-term ms unknown = just unknown


  aux : List (Maybe Term) × List (Arg Term) → Arg Term → TC (List (Maybe Term) × List (Arg Term))
  aux (ms , ips) arg′ with traverse (inst-term ms) arg′
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
  ... | false = foldlM aux ([] , []) (premises r)
                >>= λ { (ms , prems) →
                maybe (λ ips → return ( ms , rule false (rname r)
                                      ips
                                      (filter visible? prems))) 
                      (typeError [ strErr "inst-rule" ])
                      (inst-term ms (conclusion r)) }
          where
            foldlM : ∀ {A B : Set} → (B → A → TC B) → B → List A → TC B
            foldlM f b xs = foldl (λ tcb a → tcb >>= (λ b → f b a)) (return b) xs

  norm-rule : Rule → TC Rule
  norm-rule r = rule (skolem? r) (rname r) <$> normalise (conclusion r)
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
  Proof′ = Σ Nat (λ k → Vec (Goal) k × (Vec Proof k → Proof))

  con′ : ∀ {k} (r : Rule) → Vec Proof (arity r + k) → Vec Proof (suc k)
  con′ {k} r xs = head ∷ rest
    where
      head : Proof
      head = con (rname r) ? -- (vecToList $ Vec.take (arity r) xs)
      rest : Vec Proof k
      rest = ? -- Vec.drop (arity r) xs

  DebugInfo = Maybe RuleName

  -- ----------------------------------------------------------------------------
  -- -- * define proof search function                                       * --
  -- ----------------------------------------------------------------------------

  module Extensible (isHintDB : IsHintDB) where

    open IsHintDB isHintDB

    {-# TERMINATING #-}
    solve : Term → HintDB → SearchTree Proof DebugInfo
    solve g db = solveAcc (1 , g ∷ [] , ?) nothing db
      where
        solveAcc : Proof′ → DebugInfo → HintDB → SearchTree Proof DebugInfo
        solveAcc (0     ,     [] , p) di _  = succ-leaf di (p [])
        solveAcc (suc k , g ∷ gs , p) di db = node di (mapM step (getHints db))
          where
            step : Hint → TC (SearchTree Proof DebugInfo)
            step h = catchTC (inst-rule (getRule h)
                              >>= λ ir → unify′ g (conclusion (snd ir))
                              >>= λ _   → norm-rule (snd ir)
                              >>= λ ir  → return (solveAcc (prf ir) (just (rname (getRule h)) )db))
                             (return (fail-leaf (just (rname (getRule h))) ))
              where
                prf : Rule → Proof′
                prf r = (length (premises r) + k) , prm′ , (p ∘ con′ r)
                  where
                    prm′ = fmap unArg (listToVec (premises r))
                           v++ gs


  ----------------------------------------------------------------------------
  -- * define various search strategies                                   * --
  ----------------------------------------------------------------------------

  -- debug information collected by the proof search
  record Debug (B : Set) : Set where
    constructor debug
    field
      ix     : List Nat
      depth  : Nat
      fail?  : Bool
      info   : B

  Strategy : Set₁
  Strategy = ∀ {A B : Set} → (depth : Nat) → SearchTree A B -> TC (List A × List (Debug B))

  dfs′ : ∀ {A B : Set} → (depth : Nat) → (Nat × List Nat) → SearchTree A B -> TC (List A × List (Debug B))
  dfs′  zero   _  _                    = return ([] , [])
  dfs′ (suc k) (n , p) (fail-leaf l)   = return ([]    , [ debug (suc n ∷ p) (suc k) true l  ])
  dfs′ (suc k) (n , p) (succ-leaf l x) = return ([ x ] , [ debug (suc n ∷ p) (suc k) false l ])
  dfs′ (suc k) (n , p) (node l xs) = xs >>=
    foldlM  (λ {( m , ( ys , zs )) x → caseM dfs′ k (m , suc n ∷ p) x of λ
                                       { (y , z) → return (suc m , (ys ∷ʳ y , zs ∷ʳ z)) }})
               (0 , ([] , []))
     >>= λ { ( _ , a , b) → return (concat a , (debug (suc n ∷ p) (suc k) false l) ∷ concat b) }
     where
       foldlM : ∀ {A B : Set} → (B → A → TC B) → B → List A → TC B
       foldlM f b xs = foldl (λ tcb a → tcb >>= (λ b → f b a)) (return b) xs

  dfs : Strategy
  dfs d s = dfs′ d (0 , []) s
