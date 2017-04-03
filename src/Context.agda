open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Telescope

module Context where

  TelView : Set
  TelView = Telescope × Type

  Ctx = List (Arg Type)

  private
    mkContext : Ctx → TC (List (Arg Type))
    mkContext c =
      snd <$> foldlM (λ {(i , xs) (arg info t) → do t ← inferType (var i [])
                                                    -| return ((suc i) , (arg info t ∷ xs))})
                  (0 , []) c
      where
        foldlM : ∀ {A B : Set} → (B → A → TC B) → B → List A → TC B
        foldlM f b xs = foldl (λ tcb a → tcb >>= (λ b → f b a)) (return b) xs


    {-# TERMINATING #-}
    mutual
      appArg : (Nat → Nat) → Arg Term → Arg Term
      appArg s (arg i x) = arg i (app s x)

      app : (Nat → Nat) → Term → Term
      app s (var x args) = var (s x) (map (appArg s) args)
      app s (con c args) = con c (map (appArg s) args)
      app s (def f args) = def f (map (appArg s) args) 
      app s (lam v (abs s₁ x)) = lam v (Abs.abs s₁ (app s x))
      app s (pat-lam cs args) = pat-lam cs args
      app s (pi a b)  = pi a b
      app s (agda-sort s₁) = agda-sort s₁
      app s (lit l)   = lit l
      app s (meta x args) = meta x (map (appArg s) args)
      app s unknown = unknown

  toTelView : (hole : Term) → TC (TelView × Nat × Ctx)
  toTelView hole =
    do type ← inferType hole
    -| c    ← getContext
    -| ctx  ← mkContext c
    -| case telView type of λ
        { (args , t)  → return ((map (appArg (_+ (length args))) ctx
                                ++
                                snd ( foldr (λ {a (s , xs) → (suc ∘′ s , appArg s a ∷ xs)}) (suc , []) args)  , t)
                                    , length args
                                    , reverse c ++ args)}
