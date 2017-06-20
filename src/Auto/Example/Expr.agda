open import Auto
open import Data.Nat

module Auto.Example.Expr where

data Expr : Set where
  Const : ℕ → Expr
  Plus  : Expr → Expr → Expr

data Eval : Expr → ℕ → Set where
  EvalConst : ∀ {n} → Eval (Const n) n
  EvalPlus  : ∀ {e₁ e₂ n₁ n₂} → Eval e₁ n₁ → Eval e₂ n₂ → Eval (Plus e₁ e₂) (n₁ + n₂)


hintDB : HintDB
hintDB = constructors Eval

example₁ : Eval (Plus (Const 8) (Const 0)) 8
example₁ = debug (auto 10 hintDB)

example₂ : Eval (Plus (Const 8) (Const 0)) 8
example₂ = EvalPlus {!!} {!!}
