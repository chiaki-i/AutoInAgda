open import Function     using (const; id; _∘_)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; TelView; toTelView; Ctx )
open import Data.List    using ([]; [_]; _++_; _∷_; List; downFrom; map; reverse; length; foldl; foldr)
open import Data.Nat     using (ℕ; suc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit    using (⊤)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.String  using (String)
open import Reflection
open import Data.TC.Extra

module Auto where

open import Auto.Extensible simpleHintDB public using (HintDB; _<<_; ε; dfs) renaming (auto to auto′)

-- auto by default uses depth-first search
auto = auto′ dfs

private
  assembleError : List ErrorPart → List ErrorPart
  assembleError = _++ strErr "\n--------------- ⇓ ⇓ ⇓ IGNORE ⇓ ⇓ ⇓ ---------------" ∷ []

  unsupportedSyntaxError    : ∀ {A : Set} → TC A
  unsupportedSyntaxError    = typeError (assembleError [ strErr "Error: Unsupported syntax." ])

  searchSpaceExhaustedError : ∀ {A : Set} → TC A
  searchSpaceExhaustedError = typeError (assembleError [ strErr "Error: Search space exhausted, solution not found." ])

  Auto = TelView × ℕ → TC (String × Maybe Term)

  showInfo : Auto → Term × Ctx → TelView × ℕ → TC ⊤
  showInfo a (h , c) tv = caseM a tv of λ
    { (d , just x ) → typeError (assembleError (strErr "Success Solution found. The trace generated is:" ∷
                                                strErr d ∷ []))
    ; (d , nothing) → typeError (assembleError (strErr "Error: Solution not found. The trace generated is:" ∷
                                                strErr d ∷ []))}

  printTerm : Auto → Term × Ctx → TelView × ℕ → TC ⊤
  printTerm a (h , c)  tv = caseM a tv of λ
    { (_ , nothing)  → searchSpaceExhaustedError
    ; (_ , just t)   → typeError (assembleError (strErr "Success: The Term found by auto is:\n" ∷ termErr t ∷ []))}

  applyTerm : Auto → Term × Ctx → TelView × ℕ → TC ⊤
  applyTerm a (h , c) tv = caseM a tv of λ
    { (_ , nothing)   → searchSpaceExhaustedError
    ; (_ , just term) → inContext (reverse c) (unify h term)}


  run : Auto → (Auto → Term × Ctx → TelView × ℕ → TC ⊤) → Term → TC ⊤
  run a r hole = do t  ← inferType hole
                 -| c  ← getContext
                 -| caseM toTelView hole of λ
                      { (tv , n , cc ) → inContext cc (r a (hole , c) (tv , n))}

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
