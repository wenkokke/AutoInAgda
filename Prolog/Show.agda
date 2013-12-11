open import Function using (_∘_; _$_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Fin using (Fin; toℕ)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map; foldr; intersperse)
open import Data.Vec using (Vec; []; _∷_; toList) renaming (map to vmap)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

module Prolog.Show
  (Name : Set)
  (showName : Name → String)
  (Sym : ℕ → Set)
  (showSym : ∀ {n} → Sym n → String)
  (decEqSym : ∀ {k} (f g : Sym k) → Dec (f ≡ g)) where

open import Prolog Name Sym decEqSym
open import Unification.Show Sym showSym decEqSym public

joinBy : String → List String → String
joinBy sep = concat ∘ intersperse sep
  where
    concat : List String → String
    concat = foldr (_++_) ""

ppWrap : String → String → String → String
ppWrap o c s = o ++ c ++ s

ppBraces : String → String
ppBraces p = ppWrap "{" p "}"

ppParens : String → String
ppParens p = ppWrap "(" p ")"

showEnv : ∀ {m} → Vec (Term 0) m → String
showEnv = ppBraces ∘ joinBy ";" ∘ map showTerm ∘ toList

showTrace : Rules → String
showTrace = joinBy ";" ∘ map (showName ∘ name ∘ proj₂)

-- TODO
--   I believe that there's a simple way to fix this termination checker
--   issue, as we've discussed this problem in class (it's due to the map), but
--   since it's really just a show function I won't bother.

{-# NO_TERMINATION_CHECK #-}
showProof : Proof → String
showProof (con n ps) = showName n ++ ppParens (joinBy "," ∘ map showProof $ ps)

showAsProof : Rules → String
showAsProof rs with (toProof rs)
... | just p  = showProof p
... | nothing = "-"

showAns : ∀ {m} → Vec (Term 0) m × Rules → String
showAns (env , rs) = showEnv env ++ " by " ++ showAsProof rs

showList : ∀ {ℓ} {A : Set ℓ} (show : A → String) → List A → String
showList show [] = ""
showList show (x ∷ []) = show x
showList show (x ∷ y ∷ xs) = show x ++ " , " ++ showList show (y ∷ xs)
