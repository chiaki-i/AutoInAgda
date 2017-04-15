open import Prelude
open import Prelude.Extra
open import Builtin.Reflection
open import Tactic.Reflection.Telescope

module Context where

  TelView : Set
  TelView = Telescope × Type

  Ctx = List (Arg Type)

  private
    mkContext : Ctx → TC (List (Arg Type))
    mkContext c =
      snd <$> foldlM (λ {(i , xs) (arg info t) →
                        do t ← inferType (var i [])
                        -| return ((suc i) , (arg info t ∷ xs))})
                     (0 , []) c


    {-# TERMINATING #-}
    app : (Nat → Nat) → Term → Term
    app s (var x args) =  var (s x) (map (fmap (app s)) args)
    app s (con c args) = con c (map (fmap (app s)) args)
    app s (def f args) = def f (map (fmap (app s)) args) 
    app s (lam v (abs s₁ x)) = lam v (Abs.abs s₁ (app s x))
    app s (pat-lam cs args) = pat-lam cs args
    app s (pi a b)       = pi a b
    app s (agda-sort s₁) = agda-sort s₁
    app s (lit l)        = lit l
    app s (meta x args)  = meta x (map (fmap (app s)) args)
    app s unknown = unknown

  toTelView : (hole : Term) → TC (TelView × Nat × Ctx)
  toTelView hole =
    do type ← inferType hole >>= normalise
    -| c    ← getContext
    -| ctx  ← mkContext c
    -| case telView type of λ
        { (args , t)  → return ((map (fmap (app (_+ (length args)))) ctx
                                ++
                                snd ( foldr (λ {a (s , xs) → (suc ∘′ s , fmap (app s) a ∷ xs)}) (suc , []) args)  , t)
                                    , length args
                                    , reverse c ++ args)}
