open import Data.Nat
open import Data.Product
open import Auto

module Auto.Example.Nat where

postulate P : ℕ → Set


postulate Ax : ∀ {n} → P n

-- Only works with p explicit
example : (∀ {n} → P n) → P 0
example p = apply (auto 5 ε)

example5 : P 0
example5 = apply (auto 5 (ε << Ax))


-- if the {n} is passed hidde after the function
-- argument this is not working
example2 : ∀ {n} → (∀ {m} → P m) → P n
example2  p = apply (auto 5 ε)

postulate P₂ : ℕ → ℕ → Set

-- this shouldn't give us warnings
example3 : (∀ {n} → ∀ {m} → P₂ n m) → P₂ 0 1
example3  = apply (auto 5 ε)

-- this one should work out
example6 : (∀ {m n} → P₂ m n) → (∀ {n m} → P₂ n m)
example6 x = apply (auto 5 ε)

-- this one should also work however ...
example4 : ∀ {n} → (∀ {m} → P₂ n m) → P₂ n 0
example4 = apply (auto 5 ε)

data Q : Set where
  q : ∀ {n : ℕ} → P n → Q

example₂ : P 0 → Q
example₂ = apply (auto 5 (ε << q))

data R : (ℕ → Set) → Set where
  r : ∀ {n : ℕ} → P n → R P

exam1 : P 0 → R P
exam1 = apply (auto 5 (ε << r))

data S (P : ℕ → Set) : Set where
  s : ∀ {n : ℕ} → P n → S P

-- print the rules of the hint db
-- exam2 : P 0 → S P
-- exam2 p = apply (auto 5 (ε << s))

natInd : ∀ (P : ℕ → Set) → P 0 → (∀ {n} → P n → P (suc n)) → ∀ {n} → P n
natInd P pz ps {zero} = pz
natInd P pz ps {suc n} = natInd (λ z → P (suc z)) (ps pz) (λ {n} → ps)

