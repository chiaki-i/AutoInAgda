open import Function     using (const; id; _∘_)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; TelView; toTelView; Ctx; agda2goal×premises )
open import Data.List    using ([]; [_]; _++_; _∷_; List; downFrom; map; reverse; length; foldl; foldr)
open import Data.Nat     using (ℕ; suc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit    using (⊤)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.String  using (String)

open import Reflection
open import MinPrelude
open import MinPrelude.Reflection

module Auto where

  open import Auto.Extensible simpleHintDB public using (_∙_; HintDB; _<<_; ε; dfs; printDB; constructors; fromRules) renaming (auto to auto′)

  private
    assembleError : List ErrorPart → List ErrorPart
    assembleError = _++ strErr "\n--------------- ⇓ ⇓ ⇓ IGNORE ⇓ ⇓ ⇓ ---------------" ∷ []

    searchSpaceExhaustedError : ∀ {A : Set} → TC A
    searchSpaceExhaustedError = typeError (assembleError [ strErr "Error: Search space exhausted, solution not found." ])

    Auto = TelView × ℕ → TC (String × Maybe Term)

    debugAuto : Auto → Term × Ctx → TelView × ℕ → TC ⊤
    debugAuto a (h , c) tv = caseM a tv of λ
      { (d , just x ) → typeError (assembleError (strErr "Success Solution found. The trace generated is:" ∷
                                                  strErr d ∷ []))
      ; (d , nothing) → typeError (assembleError (strErr "Error: Solution not found. The trace generated is:" ∷
                                                  strErr d ∷ []))}

    applyAuto : Auto → Term × Ctx → TelView × ℕ → TC ⊤
    applyAuto a (h , c) tv = caseM a tv of λ
      { (_ , nothing)   → searchSpaceExhaustedError
      ; (_ , just term) → inContext (reverse c) (unify h term)}


    run : ∀ {A : Set} → A → (A → Term × Ctx → TelView × ℕ → TC ⊤) → Term → TC ⊤
    run a r hole = do c  ← getContext
                  -| caseM toTelView hole of λ
                        { (tv , n , cc ) → inContext cc (r a (hole , c) (tv , n))}

    DB = HintDB → TC String

    printHintDB : HintDB → Term × Ctx → TelView × ℕ → TC ⊤
    printHintDB db _ (tv , n)
      with agda2goal×premises tv
    ... | (g , args) = return (fromRules args ∙ db)
                    >>= quoteTC
                    >>= normalise
                    >>= λ t → typeError (assembleError (strErr "Goal in context:" ∷ termErr g ∷ strErr "\nRules in context" ∷ termErr t ∷ [] ))

  auto = auto′ dfs

  macro
    -- -- show debugging information.
    debug : Auto → (Term → TC ⊤)
    debug m = run m debugAuto

    -- apply the Term found if any.
    apply : Auto → (Term → TC ⊤)
    apply m = run m applyAuto

    -- print the goal and HintDB.
    print : HintDB → (Term → TC ⊤)
    print db = run db printHintDB 
