open import Level                      using (Level)
open import Function                   using (_∘_; id; flip)
open import Data.Fin     as Fin        using (fromℕ)
open import Data.Nat     as Nat        using (ℕ; suc; zero; pred; _+_; _⊔_; decTotalOrder)
open import Data.List    as List       using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Vec     as Vec        using (Vec; []; _∷_; _∷ʳ_; reverse; initLast; toList)
open import Data.Product as Prod       using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe   as Maybe      using (Maybe; just; nothing; maybe)
open import Data.Maybe.Extra           using (_<$>_)
open import Data.Sum     as Sum        using (_⊎_; inj₁; inj₂)
open import Data.Integer as Int        using (ℤ; -[1+_]; +_) renaming (_≟_ to _≟-Int_)
open import Data.Unit    as Unit       using (⊤)
open import Data.String                using (String)
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary            using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Reflection renaming (Term to AgTerm; Type to AgType; _≟_ to _≟-AgTerm_; bindTC to _>>=_; returnTC to return)

module Auto.Core where

  open DecTotalOrder decTotalOrder using (total)

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b Level.⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B


  -- define term names for the term language we'll be using for proof
  -- search; we use standard Agda names, together with term-variables
  -- and Agda implications/function types.
  data TermName : Set₀ where
    name   : (n : Name) → TermName
    var    : (i : ℤ)    → TermName
    impl   : TermName

  tname-injective : ∀ {x y} → TermName.name x ≡ TermName.name y → x ≡ y
  tname-injective refl = refl

  tvar-injective : ∀ {i j} → TermName.var i ≡ TermName.var j → i ≡ j
  tvar-injective refl = refl

  _≟-TermName_ : (x y : TermName) → Dec (x ≡ y)
  (name x) ≟-TermName (name  y) with x ≟-Name y
  (name x) ≟-TermName (name .x) | yes refl = yes refl
  (name x) ≟-TermName (name  y) | no  x≠y  = no (x≠y ∘ tname-injective)
  (name _) ≟-TermName (var   _) = no (λ ())
  (name _) ≟-TermName (impl   ) = no (λ ())
  (var  _) ≟-TermName (name  _) = no (λ ())
  (var  i) ≟-TermName (var   j) with i ≟-Int j
  (var  i) ≟-TermName (var  .i) | yes refl = yes refl
  (var  i) ≟-TermName (var   j) | no i≠j = no (i≠j ∘ tvar-injective)
  (var  _) ≟-TermName (impl   ) = no (λ ())
  (impl  ) ≟-TermName (name  _) = no (λ ())
  (impl  ) ≟-TermName (var   _) = no (λ ())
  (impl  ) ≟-TermName (impl   ) = yes refl

  -- define rule names for the proof terms/rules that our proof search will
  -- return/use; we'll use standard Agda names, together with rule-variables.
  data RuleName : Set where
    name  : Name → RuleName
    var   : ℕ    → RuleName

  name-injective : ∀ {x y} → RuleName.name x ≡ name y → x ≡ y
  name-injective refl = refl

  rvar-injective : ∀ {x y} → RuleName.var x ≡ var y → x ≡ y
  rvar-injective refl = refl

  _≟-RuleName_ : (x y : RuleName) → Dec (x ≡ y)
  name x ≟-RuleName name y = map′ (cong name) name-injective (x ≟-Name y)
  name x ≟-RuleName var  y = no (λ ())
  var  x ≟-RuleName name y = no (λ ())
  var  x ≟-RuleName var  y = map′ (cong var) rvar-injective (x Nat.≟ y)

  -- now we can load the definitions from proof search
  open import ProofSearch RuleName TermName _≟-TermName_ Literal _≟-Lit_
    as PS public renaming (Term to PsTerm; module Extensible to PsExtensible)

  -- dictionary for the treatment of variables in conversion from Agda
  -- terms to terms to be used in proof search.
  ConvertVar  : Set
  ConvertVar  = (depth index : ℕ) → ∃ PsTerm

  -- conversion dictionary for rule-terms, which turns every variable
  -- that is within the scope of the term (i.e. is defined within the
  -- term by lambda abstraction) into a variable, and every variable
  -- which is defined out of scope into a Skolem constant (which
  -- blocks unification).
  convertVar4Term : ConvertVar
  convertVar4Term = fromVar
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar d i with total i d
      fromVar d i | inj₁ i≤d = (suc (Δ i≤d) , var (fromℕ (Δ i≤d)))
      fromVar d i | inj₂ i>d = (0 , con (var (-[1+ Δ i>d ])) [])

  -- conversion dictionary for goal-terms, which turns all variables
  -- into Skolem constants which blocks all unification.
  convertVar4Goal : ConvertVar
  convertVar4Goal = fromVar
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar d i with total i d
      fromVar d i | inj₁ i≤d = (0 , con (var (+ Δ i≤d)) [])
      fromVar d i | inj₂ i>d = (0 , con (var (-[1+ Δ i>d ])) [])


  -- helper function for converting definitions or constructors to
  -- proof terms.
  fromDefOrCon : (s : Name) → ∃[ n ] List (PsTerm n) → ∃ PsTerm
  fromDefOrCon f (n , ts) = n , con (name f) ts


  -- specialised function to convert literals of natural numbers
  -- (since they have a representation using Agda names)
  convertℕ : ∀ {k} → ℕ → PsTerm k
  convertℕ  zero   = con (name (quote zero)) []
  convertℕ (suc n) = con (name (quote suc)) (convertℕ n ∷ [])


  -- convert an Agda term to a term, abstracting over the treatment of
  -- variables with an explicit dictionary of the type `ConvertVar`---
  -- passing in `ConvertVar4Term` or `ConvertVar4Goal` will result in
  -- rule-terms or goal-terms, respectively.
  mutual
    convert : ConvertVar → (depth : ℕ) → AgTerm → Maybe (∃ PsTerm)
    convert cv d (lit (nat n)) = just (0 , convertℕ n)
    convert cv d (lit l)       = just (0 , lit l)
    convert cv d (var i [])    = just (cv d i)
    convert cv d (var i args)  = nothing
    convert cv d (con c args)  = fromDefOrCon c <$> convertChildren cv d args
    convert cv d (def f args)  = fromDefOrCon f <$> convertChildren cv d args
    convert cv d (pi (arg (arg-info visible _) t₁) (abs _ t₂))
      with convert cv d t₁ | convert cv (suc d) t₂
    ... | nothing | _         = nothing
    ... | _        | nothing  = nothing
    ... | just (n₁ , p₁) | just (n₂ , p₂)
      with match p₁ p₂
    ... | (p₁′ , p₂′) = just (n₁ ⊔ n₂ , con impl (p₁′ ∷ p₂′ ∷ []))
    convert cv d (pi (arg _ _) (abs _ t₂)) = convert cv (suc d) t₂
    convert cv d (lam _ _)     = nothing
    convert cv d (pat-lam _ _) = nothing
    convert cv d (sort _)      = nothing
    convert cv d unknown       = nothing
    convert cv d (meta _ _)    = nothing

    convertChildren :
      ConvertVar → ℕ → List (Arg AgTerm) → Maybe (∃[ n ] List (PsTerm n))
    convertChildren cv d [] = just (0 , [])
    convertChildren cv d (arg (arg-info visible _) t ∷ ts)
      with convert cv d t | convertChildren cv d ts
    ... | nothing       | _             = nothing
    ... | _             | nothing       = nothing
    ... | just (m , p)  | just (n , ps) with match p ps
    ... | (p′ , ps′)                     = just (m ⊔ n , p′ ∷ ps′)
    convertChildren cv d (arg _ _ ∷ ts)  = convertChildren cv d ts


  -- split a term at every occurrence of the `impl` constructor---
  -- equivalent to splitting at every occurrence of the _→_ symbol in
  -- an Agda term.
  split : ∀ {n} → PsTerm n → ∃[ k ] Vec (PsTerm n) (suc k)
  split (con impl (t₁ ∷ t₂ ∷ [])) = Prod.map suc (λ ts → t₁ ∷ ts) (split t₂)
  split t = zero , t ∷ []


  -- convert an Agda term to a goal-term, together with a `HintDB`
  -- representing the premises of the rule---this means that for a
  -- term of the type `A → B` this function will generate a goal of
  -- type `B` and a premise of type `A`.
  agda2goal×premises : AgType →  Maybe (∃ PsTerm × Rules)
  agda2goal×premises t with convert convertVar4Goal 0 t
  ... | nothing             = nothing
  ... | just (n , p)        with split p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = just ((n , goal) , toPremises (pred k) prems)
    where
      toPremises : ∀ {k} → ℕ → Vec (PsTerm n) k → Rules
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (var i) t []) ∷ toPremises (pred i) ts


  -- A context is a deBruijn indexed list of the types of the variables.
  Ctx = List (AgType)


  -- convert an Agda context to a `HintDB`.
  context2premises : (index : ℕ) → Ctx → Maybe Rules
  context2premises i []       = just []
  context2premises i (t ∷ ts)
    with convert convertVar4Goal 0 t
  ... | nothing          = context2premises (suc i) ts
  ... | just (n , p)     with split p
  ... | (k , ts')        with initLast ts'
  ... | (prems , goal , _) with context2premises (suc i) ts
  ... | nothing            = just ((n , rule (var i) goal (toList prems)) ∷ [])
  ... | just xs            = just ((n , rule (var i) goal (toList prems)) ∷ xs)


  -- convert an Agda name to a rule-term.
  name2term : Name → AgType → Maybe (∃ Rule)
  name2term nm ty with convert convertVar4Term 0 ty
  ... | nothing            = nothing
  ... | just (n , t)        with split t
  ... | (k , ts)            with initLast ts
  ... | (prems , concl , _) = just (n , rule (name nm) concl (toList prems))


  -- function which reifies untyped proof terms (from the
  -- `ProofSearch` module) to untyped Agda terms.
  mutual
    proof2AgTerm : Proof → TC AgTerm
    proof2AgTerm (con (var i) ps)  = return (var i [])
    proof2AgTerm (con (name n) ps) =
      getDefinition n >>=
        λ { (function cs)       → children2AgTerms ps >>= (return ∘ def n)
          ; (constructor′ d)    → children2AgTerms ps >>= (return ∘ con n) 
          ; (data-type pars cs) → return unknown
          ; (record′ c)         → return unknown
          ; axiom               → return unknown
          ; primitive′          → return unknown }

    children2AgTerms : List Proof → TC (List (Arg AgTerm))
    children2AgTerms []       = return []
    children2AgTerms (p ∷ ps) = proof2AgTerm p
                              >>= λ r  → children2AgTerms ps
                              >>= λ cs → return (toArg r ∷ cs)
      where
        toArg : AgTerm → Arg AgTerm
        toArg = arg (arg-info visible relevant)

  intros : ℕ → AgTerm → AgTerm
  intros  zero   t = t
  intros (suc k) t = lam visible (abs "_" ((intros k t)))

  reify : ℕ → Proof → TC AgTerm
  reify n p = proof2AgTerm p >>= (return ∘ intros n)

  -- debugging facilities
  Debug = String

  debug2String : Debug → String
  debug2String = λ x → x
