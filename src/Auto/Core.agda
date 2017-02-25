open import Level                      using (Level)
open import Function                   using (_∘_; id; flip)
open import Data.Fin     as Fin        using (fromℕ)
open import Data.Nat     as Nat        using (ℕ; suc; zero; pred; _+_; _⊔_)
open import Data.Nat.Properties        using (≤-decTotalOrder)
open import Data.List    as List       using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Vec     as Vec        using (Vec; []; _∷_; _∷ʳ_; reverse; initLast; toList)
open import Data.Product as Prod       using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe   as Maybe      using (Maybe; just; nothing; maybe)
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

  open DecTotalOrder ≤-decTotalOrder using (total)

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

  -- define our own instance of the error functor based on the either
  -- monad, and use it to propagate one of several error messages
  Error : ∀ {a} (A : Set a) → Set a
  Error A = Maybe A

  private
    _⟨$⟩_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Error A → Error B
    f ⟨$⟩ nothing = nothing
    f ⟨$⟩ just y  = just (f y)
  -- next up, converting the terms returned by Agda's reflection
  -- mechanism to terms in our proof search's language!


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
    convert : ConvertVar → (depth : ℕ) → AgTerm → Error (∃ PsTerm)
    convert cv d (lit (nat n)) = just (0 , convertℕ n)
    convert cv d (lit l)       = just (0 , lit l)
    convert cv d (var i [])    = just (cv d i)
    convert cv d (var i args)  = nothing
    convert cv d (con c args)  = fromDefOrCon c ⟨$⟩ convertChildren cv d args
    convert cv d (def f args)  = fromDefOrCon f ⟨$⟩ convertChildren cv d args
    convert cv d (pi (arg (arg-info visible _) t₁) (abs _ t₂))
      with convert cv d t₁ | convert cv (suc d) t₂
    ... | nothing | _        = nothing
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
      ConvertVar → ℕ → List (Arg AgTerm) → Error (∃[ n ] List (PsTerm n))
    convertChildren cv d [] = just (0 , [])
    convertChildren cv d (arg (arg-info visible _) t ∷ ts)
      with convert cv d t | convertChildren cv d ts
    ... | nothing      | _              = nothing
    ... | _             | nothing       = nothing
    ... | just (m , p)  | just (n , ps) with match p ps
    ... | (p′ , ps′)                      = just (m ⊔ n , p′ ∷ ps′)
    convertChildren cv d (arg _ _ ∷ ts)   = convertChildren cv d ts


  -- convert an Agda term to a rule-term.
  agda2term : AgTerm → Error (∃ PsTerm)
  agda2term t = convert convertVar4Term 0 t


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
  -- the ℕ represents the initial `depth` to convert variables as there
  -- might be variables given in the context.
  agda2goal×premises : ℕ → AgType →  Error (∃ PsTerm × Rules)
  agda2goal×premises d t with convert convertVar4Goal d t
  ... | nothing             = nothing
  ... | just (n , p)        with split p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = just ((n , goal) , toPremises (pred k) prems)
    where
      toPremises : ∀ {k} → ℕ → Vec (PsTerm n) k → Rules
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (var i) t []) ∷ toPremises (pred i) ts

  Ctx = List (Arg AgType)

  -- convert an Agda context to a `HintDB`.
  context2premises : Ctx → Error Rules
  context2premises ctx
    with convertChildren convertVar4Goal 0 ctx
  ... | nothing = nothing
  ... | just (n , p) = just (toPremises n p)
    where
      toPremises : ℕ → List (PsTerm n) → Rules
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (var i) t []) ∷ toPremises (pred i) ts

  -- convert an Agda name to a rule-term.
  name2term : Name → AgType → Error (∃ Rule)
  name2term nm ty with agda2term ty
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
    children2AgTerms (p ∷ ps) = proof2AgTerm p >>= (λ r → children2AgTerms ps >>= (λ cs → return (toArg r ∷ cs)))
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
