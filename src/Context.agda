open import Data.List      using (List; _∷_; []; map; length; foldr; _++_; reverse)
open import Data.Nat       using (ℕ ; suc; zero; _+_; pred; compare)
open import Function       using (_∘′_; case_of_)
open import Data.Product   using (_×_; _,_; proj₁; proj₂)

open import Steroids
open import Steroids.Reflection
open import Reflection

module Context where

  -- a TelView refers to the telescopic view of
  -- a type. A list of arguments left to the arrows
  -- plus the term at the right of them.
  TelView : Set
  TelView = List (Arg Type) × Type

  -- return a view of a pi type
  telView : Type → TelView
  telView (pi a (abs _ b)) with telView b
  ... | (l , t) = a ∷ l , t
  telView a = [] , a

  -- A context is a list of types tagged with the
  -- argument information (visibility and other stuff)
  Ctx = List (Arg Type)

  private
    -- given a context as returned by `getContext` transform it in
    -- one where the terms have the correct indexes in the variables
    mkContext : Ctx → TC Ctx
    mkContext c =
      proj₂ <$> foldlM (λ {(i , xs) (arg info t) → do t ← inferType (var i []) >>= normalise
                                                        -| return ((suc i) , (arg info t ∷ xs))})
                       (0 , []) c


    -- change the debruijn indexes of a Term with a
    -- function (ℕ → ℕ) and a base index.
    {-# TERMINATING #-}
    mutual
      appArg : ℕ → (ℕ → ℕ) → Arg Term → Arg Term
      appArg b s (arg i x) = arg i (app b s x)

      app : ℕ → (ℕ → ℕ) → Term → Term
      app b s (var x args) with compare x b
      ... | Data.Nat.less _ _ = var x (map (appArg b s) args)
      ... | _                 = var (s x) (map (appArg b s) args)
      app b s (con c args) = con c (map (appArg b s) args)
      app b s (def f args) = def f (map (appArg b s) args)
      app b s (lam v (abs s₁ x)) = lam v (abs s₁ (app b s x))
      app b s (pat-lam cs args) = pat-lam cs args
      app b s (pi a (abs s₁ x)) = pi (appArg b s a) (abs s₁ (app (1 + b) (pred ∘′ s) x))
      app b s (sort s₁) = sort s₁
      app b s (lit l)   = lit l
      app b s (meta x args) = meta x (map (appArg b s) args)
      app b s unknown = unknown


  -- given a hole, we calculate the telView of it returning
  -- the context, the number of arguments and the telView.
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
