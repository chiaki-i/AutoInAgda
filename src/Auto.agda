open import Function     using (const; id; _∘_)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; Ctx; Debug; debug2String)
open import Data.List    using ([]; [_]; _++_; _∷_; List)
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.Sum     using (inj₁; inj₂; _⊎_)
open import Data.Unit    using (⊤)
open import Data.Maybe
open import Data.String  using (String)
open import Reflection   renaming (bindTC to _>>=_)

module Auto where

open import Auto.Extensible simpleHintDB public using (auto; HintDB; _<<_; ε)

private
  assembleError : List ErrorPart → List ErrorPart
  assembleError = _++ strErr "\n--------------- ⇓ ⇓ ⇓ IGNORE ⇓ ⇓ ⇓ ---------------" ∷ []

  unsupportedSyntaxError    : ∀ {A : Set} → TC A
  unsupportedSyntaxError    = typeError (assembleError [ strErr "Error: Unsupported syntax." ])

  searchSpaceExhaustedError : ∀ {A : Set} → TC A
  searchSpaceExhaustedError = typeError (assembleError [ strErr "Error: Search space exhausted, solution not found." ])

macro
  -- show debugging information.
  info : (Type → Ctx → Maybe (Debug × Maybe (TC Term))) → (Term → TC ⊤)
  info m = λ h → inferType h >>= (λ t → getContext >>= run h t)
    where
      run : Term → Type → Ctx → TC ⊤
      run h t ctx with m t ctx
      ... | nothing = unsupportedSyntaxError
      ... | just (d , just x)      =
        typeError (assembleError (strErr "Success Solution found. The trace generated is:" ∷
                                  strErr (debug2String d) ∷ []))
      ... | just (d , nothing)     =
        typeError (assembleError (strErr "Error: Solution not found. The trace generated is:" ∷
                                  strErr d ∷ []))

  -- print the resulting Term if any found.
  print : (Type → Ctx → Maybe (String × Maybe (TC Term))) → (Term → TC ⊤)
  print m = λ h → inferType h >>= (λ t → getContext >>= run t)
    where
      run : Type → Ctx → TC ⊤
      run t ctx with m t ctx
      ... | nothing = unsupportedSyntaxError
      ... | just (_ , nothing)     = searchSpaceExhaustedError
      ... | just (_ , just x)      = x >>=
        λ t → typeError (assembleError (strErr "Success: The Term found by auto is:\n" ∷ termErr t ∷ []))

  -- apply the Term found if any.
  apply : (Type → Ctx → Maybe (String × Maybe (TC Term))) → (Term → TC ⊤)
  apply m = λ h → inferType h >>= (λ t → getContext >>= run h t)
    where
      run : Term → Type → Ctx → TC ⊤
      run h t ctx with m t ctx
      ... | nothing = unsupportedSyntaxError
      run h t ctx | just (_ , just x)      = x >>= unify h
      run h t ctx | just (_ , nothing)     = searchSpaceExhaustedError
