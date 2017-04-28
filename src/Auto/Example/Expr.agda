open import Auto
open import Data.Nat

module Auto.Example.Expr where

data Expr : Set where
  Const : ℕ → Expr
  Var   : Expr
  Plus  : Expr → Expr → Expr

data Eval (var : ℕ) : Expr → ℕ → Set where
  EvalConst : ∀ {n} → Eval var (Const n) n
  EvalVar   : Eval var Var var
  EvalPlus  : ∀ {e₁ e₂ n₁ n₂} → Eval var e₁ n₁ → Eval var e₂ n₂ → Eval var (Plus e₁ e₂) (n₁ + n₂)


hintDB : HintDB
hintDB = ε << EvalConst << EvalVar << EvalPlus

example₁ : ∀ {var} → Eval var (Plus Var (Plus (Const 8) Var)) (var + (8 + var))
example₁ = {!!} -- debug (auto 10 hintDB)

example₁′  : ∀ {var} → Eval var (Plus Var (Plus (Const 8) Var)) (var + (8 + var))
example₁′  = EvalPlus EvalVar {!!}
