open import Data.List      using (List; _∷_; []; map; length; foldr; _++_; reverse)
open import Data.Nat       using (ℕ ; suc; zero; _+_)
open import Function       using (_∘′_; case_of_)
open import Data.Product   using (_×_; _,_; proj₁; proj₂)

open import Reflection
open import Data.TC.Extra

module Context where

  TelView : Set
  TelView = List (Arg Type) × Type

  Ctx = List (Arg Type)

  private 
    mkContext : Ctx → TC (List (Arg Type))
    mkContext c =
      proj₂ <$-tc> foldlM-tc (λ {(i , xs) (arg info t) → do t ← inferType (var i []) >>= normalise
                                                        -| return ((suc i) , (arg info t ∷ xs))})
                  (0 , []) c



    {-# TERMINATING #-}
    mutual
      appArg : (ℕ → ℕ) → Arg Term → Arg Term
      appArg s (arg i x) = arg i (app s x)

      app : (ℕ → ℕ) → Term → Term
      app s (var x args) = var (s x) (map (appArg s) args)
      app s (con c args) = con c (map (appArg s) args)
      app s (def f args) = def f (map (appArg s) args) 
      app s (lam v (abs s₁ x)) = lam v (abs s₁ (app s x))
      app s (pat-lam cs args) = pat-lam cs args
      app s (pi a b)  = pi a b
      app s (sort s₁) = sort s₁
      app s (lit l)   = lit l
      app s (meta x args) = meta x (map (appArg s) args)
      app s unknown = unknown

  -- return a view of a pi type
  telView : Type → TelView
  telView (pi a (abs _ b)) with telView b
  ... | (l , t) = a ∷ l , t
  telView a = [] , a

  toTelView : (hole : Term) → TC (TelView × ℕ × Ctx)
  toTelView hole =
    do type ← inferType hole
    -| c    ← getContext
    -| ctx  ← mkContext c
    -| case telView type of λ
        { (args , t)  → return ((map (appArg (_+ (length args))) ctx
                                ++
                                proj₂ ( foldr (λ {a (s , xs) → (suc ∘′ s , appArg s a ∷ xs)}) (suc , []) args)  , t)
                                      , length args
                                      , reverse c ++ args)}
