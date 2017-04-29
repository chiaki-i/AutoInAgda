open import Data.List      using (List; _∷_; []; map; length; foldr; _++_; reverse)
open import Data.Nat       using (ℕ ; suc; zero; _+_; pred; compare)
open import Function       using (_∘′_; case_of_)
open import Data.Product   using (_×_; _,_; proj₁; proj₂)

open import MinPrelude
open import MinPrelude.Reflection
open import Reflection

module Context where

  TelView : Set
  TelView = List (Arg Type) × Type

  Ctx = List (Arg Type)

  private
    mkContext : Ctx → TC (List (Arg Type))
    mkContext c =
      proj₂ <$> foldlM (λ {(i , xs) (arg info t) → do t ← inferType (var i []) >>= normalise
                                                        -| return ((suc i) , (arg info t ∷ xs))})
                  (0 , []) c



    {-# TERMINATING #-}
    mutual
      appArg : ℕ → (ℕ → ℕ) → Arg Term → Arg Term
      appArg b s (arg i x) = arg i (app b s x)

      app : ℕ → (ℕ → ℕ) → Term → Term
      app b s (var x args) with compare x b 
      ... | Data.Nat.less _ _ = var x (map (appArg b s) args)
      ... | _                  = var (s x) (map (appArg b s) args)
      app b s (con c args) = con c (map (appArg b s) args)
      app b s (def f args) = def f (map (appArg b s) args) 
      app b s (lam v (abs s₁ x)) = lam v (abs s₁ (app b s x))
      app b s (pat-lam cs args) = pat-lam cs args
      app b s (pi a (abs s₁ x)) = pi (appArg b s a) (abs s₁ (app (1 + b) (pred ∘′ s) x))
      app b s (sort s₁) = sort s₁
      app b s (lit l)   = lit l
      app b s (meta x args) = meta x (map (appArg b s) args)
      app b s unknown = unknown

  -- return a view of a pi type
  telView : Type → TelView
  telView (pi a (abs _ b)) with telView b
  ... | (l , t) = a ∷ l , t
  telView a = [] , a

  toTelView : (hole : Term) → TC (TelView × ℕ × Ctx)
  toTelView hole =
    do type ← inferType hole >>= normalise
    -| c    ← getContext
    -| ctx  ← mkContext c
    -| case telView type of λ
        { (args , t)  → return ((map (appArg 0 (_+ (length args))) ctx
                                ++
                                proj₂ ( foldr (λ {a (s , xs) → (suc ∘′ s , appArg 0 s a ∷ xs)}) (suc , []) args)  , t)
                                      , length args
                                      , reverse c ++ args)}
