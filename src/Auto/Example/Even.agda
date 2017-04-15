open import Auto
open import Prelude

module Auto.Example.Even where

  data Even  : Nat →  Set where
    isEven0  : Even 0
    isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

  even+ : ∀ {n m} → Even n → Even m → Even (n + m)
  even+  isEven0      e2 = e2
  even+ (isEven+2 e1) e2 = isEven+2 (even+ e1 e2)

  isEven-2 : ∀ {n} → Even (2 + n) → Even n
  isEven-2 (isEven+2 n) = n

  simple : ∀ {n} → Even n → Even (n + 2)
  simple e =  even+ e (isEven+2 isEven0)

  rules : HintDB
  rules = ε << isEven0
            << isEven+2
            << even+
            -- << isEven-2

  test1 : Even 4
  test1 = debug (auto 6 rules)

  test₂ : Even 100
  test₂ = apply (auto 100 rules)

  test2 : ∀ {n} → Even n → Even (n + 4)
  test2 e = apply (auto 8 rules)

  test2′ : ∀ {n} → Even n → Even (2 + n)
  test2′ e = apply (auto 6 rules)

  test₃ : ∀ {n} → Even n → Even (4 + n)
  test₃ = apply (auto 6 rules)

  test₄ : ∀ {n} → Even n → Even (n + 200)
  test₄ e = apply (auto 200 rules)

  -- attempting to prove an impossible goal (e.g. evenness of n + 3
  -- for all n) will result in searchSpaceExhausted
  -- goal₁ = quoteTerm (∀ {n} → Even n → Even (n + 3))
  -- fail₁ : (auto 5 rules goal₁) ≡ throw searchSpaceExhausted
  -- fail₁ = refl

  -- attempting to convert an unsupported expression (e.g. a lambda
  -- term) will result in unsupportedSyntax
  -- goal₂ = quoteTerm (∃₂ λ m n → Even (m + n))
  -- fail₂ : unquote (auto 5 rules goal₂) ≡ throw unsupportedSyntax
  -- fail₂ = refl
