open import Auto
open import Function using (_∋_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)

module Auto.Example.Even where


  data Even  : ℕ →  Set where
    isEven0  : Even 0
    isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

  even+ : ∀ {n m} → Even n → Even m → Even (n + m)
  even+  isEven0      e2 = e2
  even+ (isEven+2 e1) e2 = isEven+2 (even+ e1 e2)

  isEven-2 : ∀ {n} → Even (2 + n) → Even n
  isEven-2 (isEven+2 n) = n

  rules : HintDB
  rules = ε << isEven0
            << isEven+2
            << even+

  test₁ : Even 4
  test₁ = apply (auto 6 rules)

  test₂ : Even 100
  test₂ = apply (auto 100 rules)

  test₃ : ∀ {n} → Even n → Even (n + 4)
  test₃ e = apply (auto 8 rules)

  test₃′ : ∀ {n} → Even n → Even (4 + n)
  test₃′ e = apply (auto 6 rules)

  test₄ : ∀ {n} → Even n → Even (n + 200)
  test₄ e = apply (auto 200 rules)

  simple : ∀ {n} → Even n → Even (4 + n)
  simple with Even 0 ∋ {!!}
  ... | _ = apply (auto 5 (ε << even+
                             << isEven+2))

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
