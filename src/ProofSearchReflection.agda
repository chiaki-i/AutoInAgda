open import Data.List as List
open import Reflection
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Unit
open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Level                                 using (_⊔_)
open import Function                              using (id; const; _∘_; _$_)
open import Data.Vec        as Vec                using (Vec; _∷_; []; fromList)
open import Data.TC.Extra
open import Data.Maybe.Extra
open import Data.List.Extra
open import Data.Bool

module ProofSearchReflection
  (RuleName : Set )
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

    newMetaArg : Arg Term → TC Meta
    newMetaArg (arg i x) = newMeta x
      >>= (λ { (meta m [])    → return m
             ; _              → typeError (strErr "newMetaArg" ∷ []) })

    unArg : ∀ {A : Set} → Arg A → A
    unArg (arg i x) = x

    {-# TERMINATING #-}
    inst-term : List Meta → Term → Maybe Term
    inst-term ms (var x args)  = meta <$-m> index ms x
                                      <*-m> mapM-m (traverse-m-arg (inst-term ms))
                                            args
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
    inst-term ms (meta x args) = meta x <$-m> mapM-m (traverse-m-arg (inst-term ms))                                             args
    inst-term ms unknown = just unknown


    aux : List Meta × List (Arg Term) → Arg Term → TC (List Meta × List (Arg Term))
    aux (ms , ips) a with traverse-m-arg (inst-term ms) a
    ... | nothing = typeError [ strErr "aux" ]
    ... | just ip = newMetaArg ip >>= (λ m → return ((m ∷ ms) , ips ∷ʳ ip))


    inst-rule : Rule → TC Rule
    inst-rule r with skolem? r
    ... | true  = return (rule true
                               (rname r)
                               (conclusion r)
                               (filter visible? (premises r)))
    ... | false = foldlM-tc aux ([] , []) (premises r)
                  >>= λ { (ms , prems) →
                  maybe (λ ips → return (rule false (rname r)
                                        ips
                                        (filter visible? prems))) 
                        (typeError [ strErr "inst-rule" ])
                        (inst-term ms (conclusion r)) }

    unify-concl : Term → Rule → TC Bool
    unify-concl t r = catchTC (unify (conclusion r) t >>= λ _ → return true)
                            (return false)
  -- ----------------------------------------------------------------------------
  -- -- * define simple hint databases                                       * --
  -- ----------------------------------------------------------------------------

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
  data SearchTree (A : Set) : Set where
    leaf : A → SearchTree A
    node : TC (List (SearchTree A)) → SearchTree A

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


  -- ----------------------------------------------------------------------------
  -- -- * define proof search function                                       * --
  -- ----------------------------------------------------------------------------

  module Extensible (isHintDB : IsHintDB) where

    open IsHintDB isHintDB

    {-# TERMINATING #-}
    solve : Term → HintDB → SearchTree Proof
    solve g = solveAcc (1 , g ∷ [] , Vec.head)
      where
        solveAcc : Proof′ → HintDB → SearchTree Proof
        solveAcc (0     ,     [] , p) _  = leaf (p [])
        solveAcc (suc k , g ∷ gs , p) db = node (mapM-tc step (getHints db))
          where
            step : Hint → TC (SearchTree (Proof))
            step h =   inst-rule (getRule h)
                   >>= λ ir → unify-concl g ir
                   >>= λ { false  → return (node (return []))
                         ; true   → return (solveAcc 
                                           (prf ir)
                                           db)}
              where
                prf : Rule → Proof′
                prf r = (length (premises r) + k) , prm′ , (p ∘ con′ r)
                  where
                    prm′ = Vec.map unArg (Vec.fromList (premises r))
                           Vec.++ gs


  ----------------------------------------------------------------------------
  -- * define various search strategies                                   * --
  ----------------------------------------------------------------------------
  Strategy = ∀ {A : Set} → (depth : ℕ) → SearchTree A -> TC (List A)

  dfs : ∀ {A : Set} → (depth : ℕ) → SearchTree A -> TC (List A)
  dfs  zero    _        = return []
  dfs (suc k) (leaf x)  = return (x ∷ [])
  dfs (suc k) (node xs) =
    xs >>= λ xs′ → List.concat <$-tc> sequence-tc (List.map (dfs k) xs′)

  -- -- macro
  -- --   n : Name → Term → TC ⊤
  -- --   n nm h = name2rule nm >>= (λ {(just x) → quoteTC x >>= (λ t → unify t h)
  -- --                                ; nothing → typeError [ strErr "nm" ]})

  -- --   inst : Rule PsTerm → Term → TC ⊤
  -- --   inst r h = inst-rule r >>= (λ x → quoteTC x >>= (λ t → normalise t >>= λ a → typeError [ termErr a ]))

  -- --   getTDef : Name → Term → TC ⊤
  -- --   getTDef nm h = getType nm >>= quoteTC >>= λ t → normalise t >>= λ t → typeError (termErr t ∷ []) 



  -- -- sequence-TC : ∀ {A : Set} → List (TC A) → TC (List A)
  -- -- sequence-TC []       = return []
  -- -- sequence-TC (x ∷ xs) = x >>= (λ x′ → sequence-TC xs >>= (λ xs′ → return (x′ ∷ xs′)))


  -- -- safe-head : ∀ {A : Set} → List A → Maybe A
  -- -- safe-head [] = nothing
  -- -- safe-head (x ∷ _) = just x

  -- -- macro
  -- --   auto : (depth : ℕ) → HintDB → Term → TC ⊤
  -- --   auto depth db h = inferType h >>= (λ t → safe-head <$-tc> (dfs depth (solve t db)) >>=  λ ls → quoteTC ls >>= λ ls → normalise ls  >>= (λ ls' → typeError ([ termErr ls' ]))) 

  -- -- db : HintDB
  -- -- db = isEven0-rule ∷ isEven+2-rule ∷ even+-rule ∷ []

  -- -- example3 : Even 20
  -- -- example3 = {!auto 12 db!}
