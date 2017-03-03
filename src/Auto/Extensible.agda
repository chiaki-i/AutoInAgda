open import Auto.Core
open import Function     using (_∘_; const)
open import Data.List    using (_∷_; []; List; length; takeWhile; reverse; map; foldr; intersperse)
open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Product using (∃; _,_; Σ; _×_)
open import Data.Sum     using (inj₁; inj₂; _⊎_)
open import Data.Unit    using (⊤)
open import Data.String  using (String; _++_; toList; fromList; unlines)
open import Data.Char    using (_==_)
open import Data.Bool
open import Reflection   using (Type; Term; Arg; Name; TC; quoteTC; getType; termErr; showName)
                         renaming (bindTC to _>>=_; returnTC to return; unify to unifyTC)

open import Data.Maybe using (Maybe; just; nothing)

module Auto.Extensible (instHintDB : IsHintDB) where


open IsHintDB     instHintDB public renaming (return to returnHintDB)
open PsExtensible instHintDB public
open Auto.Core               public using (dfs; bfs)

showL : List ℕ → String
showL  = foldr _++_ "" ∘ intersperse "." ∘ map showNat

showB : Bool → String
showB false = "✓"
showB true  = "×"

showD : (List ℕ × Bool × Maybe RuleName × ℕ) → String
showD (l , b , nm , d) with nm
... | just (name x) = showL (reverse l) ++ " depth=" ++ showNat d ++ " "     ++ strip (showName x) ++ " " ++ showB b
  where
    strip : String → String
    strip = fromList ∘ reverse ∘ takeWhile (not ∘ (_== '.')) ∘ reverse ∘ toList
... | just (var x)  = showL (reverse l) ++ " depth=" ++ showNat d ++ " var " ++ showNat x ++ " " ++ showB b
... | nothing = ""

auto : ℕ → HintDB → Type → Ctx → Maybe (Debug × Maybe (TC Term))
auto depth db type ctx
  with agda2goal×premises type
... | nothing = nothing
... | just ((n , g) , args)
  with context2premises (length args) ctx
... | nothing = nothing
... | just ctxs
  with dfs (suc depth) (solve g (fromRules ctxs ∙ (fromRules args ∙ db))) 
... | ([] , d)    = just ((unlines ∘ map showD) d , nothing)
... | (p ∷ _ , d) = just ((unlines ∘ map showD) d , just (reify (length args) p)) 

_<<<_ : HintDB → Error (∃ Rule) → HintDB
db <<< nothing      = db
db <<< just (_ , r) = (returnHintDB r) ∙ db

infixl 5 _<<_

infixl 5 _<<<_

macro
  _<<_ : HintDB → Name → (Term → TC ⊤)
  db << nm = λ h → (getType nm >>= (λ t → quoteTC (db <<< (name2term nm t)) >>= unifyTC h ))
