open import Function     using (const; id; _∘_)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; Ctx)
open import Data.List    using ([]; [_]; _++_; _∷_; List; downFrom; map; reverse; length)
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.Sum     using (inj₁; inj₂; _⊎_)
open import Data.Unit    using (⊤)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.String  using (String)
open import Reflection
open import Data.TC.Extra

module Auto where

open import Auto.Extensible simpleHintDB public using (HintDB; _<<_; ε; dfs) renaming (auto to auto′)

-- auto by default uses depth-first search
auto = auto′ dfs

-- This is exported to debug for now

mkContext : ℕ → TC (List Type)
mkContext = (mapM-tc inferType) ∘ reverse ∘ map (λ x → var x []) ∘ downFrom

private
  assembleError : List ErrorPart → List ErrorPart
  assembleError = _++ strErr "\n--------------- ⇓ ⇓ ⇓ IGNORE ⇓ ⇓ ⇓ ---------------" ∷ []

  unsupportedSyntaxError    : ∀ {A : Set} → TC A
  unsupportedSyntaxError    = typeError (assembleError [ strErr "Error: Unsupported syntax." ])

  searchSpaceExhaustedError : ∀ {A : Set} → TC A
  searchSpaceExhaustedError = typeError (assembleError [ strErr "Error: Search space exhausted, solution not found." ])

  Auto = Type → Ctx → TC (String × Maybe Term)

  showInfo : Auto → Term → Type → Ctx → TC ⊤
  showInfo a h t ctx = caseM a t ctx of λ
    { (d , just x ) → typeError (assembleError (strErr "Success Solution found. The trace generated is:" ∷
                                                strErr d ∷ []))
    ; (d , nothing) → typeError (assembleError (strErr "Error: Solution not found. The trace generated is:" ∷
                                                strErr d ∷ []))}

  printTerm : Auto → Term → Type → Ctx → TC ⊤
  printTerm a h t ctx = caseM a t ctx of λ
    { (_ , nothing)  → searchSpaceExhaustedError
    ; (_ , just t)   → typeError (assembleError (strErr "Success: The Term found by auto is:\n" ∷ termErr t ∷ []))}

  applyTerm : Auto → Term → Type → Ctx → TC ⊤
  applyTerm a h t ctx = caseM a t ctx of λ
    { (_ , nothing)   → searchSpaceExhaustedError
    ; (_ , just term) → checkType term t >>= unify h}


  run : Auto → (Auto → Term → Type → Ctx → TC ⊤) → Term → TC ⊤
  run a r h = inferType h
            >>= λ t → getContext
            >>= λ c → mkContext (length c)
            >>= λ ctx → r a h t ctx

macro
  -- -- show debugging information.
  info : Auto → (Term → TC ⊤)
  info m = run m showInfo

  -- print the resulting Term if any found.
  print : Auto → (Term → TC ⊤)
  print m = run m printTerm

  -- apply the Term found if any.
  apply : Auto → (Term → TC ⊤)
  apply m = run m applyTerm
