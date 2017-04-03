
open import Auto
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Function using (_∋_)

module Auto.Example.Plus where

-- Addition on naturals viewed as a logical relation
data Plus : ℕ → ℕ → ℕ → Set where
  plusZ : ∀ {n}     → Plus 0 n n
  plusS : ∀ {n m r} → Plus n m r → Plus (suc n) m (suc r)

Plus-HintDB : HintDB
Plus-HintDB = ε << plusS
                << plusZ

-- a handy synonym
_+ℕ_≡_ : ℕ → ℕ → ℕ → Set
n +ℕ m ≡ r = Plus n m r

c-Plus : ∀ n m r → n + m ≡ r → n +ℕ m ≡ r
c-Plus zero m .m refl = plusZ
c-Plus (suc n) m .(suc (n + m)) refl = plusS (c-Plus n m _ refl)

s-Plus : ∀ n m r → n +ℕ m ≡ r → n + m ≡ r
s-Plus .0 m .m plusZ = refl
s-Plus .(suc _) m .(suc _) (plusS p) = cong suc (s-Plus _ _ _ p)

plus-5+3=8 : ∀ {n} → 0 +ℕ n ≡ n
plus-5+3=8 = apply (auto 10 Plus-HintDB)

plus-5+1=6 : 16 +ℕ 0 ≡ 16
plus-5+1=6 = apply (auto 20 Plus-HintDB)

plus-0+1=1 : 1 +ℕ 1 ≡ 2
plus-0+1=1 with plusZ
... | _ = apply (auto 2 (ε << plusS))
