open import Function using (_∘_)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

module Unification.Show
  (Sym : ℕ → Set)
  (showSym : ∀ {k} (s : Sym k) → String)
  (decEqSym : ∀ {k} (f g : Sym k) → Dec (f ≡ g)) where

  import Unification
  module UI = Unification Sym decEqSym
  open UI hiding (_++_)

  showFin : ∀ {n} → Fin n → String
  showFin {n} x = (showℕ (toℕ x)) ++ "/" ++ (showℕ n)

  mutual
    showTerm : ∀ {n} → Term n → String
    showTerm (var x) = "?" ++ showFin x
    showTerm (con {zero} s []) = showSym s
    showTerm (con {suc k} s ts) = showSym s ++ "(" ++ showTermArgs ts ++ ")"

    showTermArgs : ∀ {n k} → Vec (Term n) k → String
    showTermArgs []             = ""
    showTermArgs (t ∷ [])       = showTerm t
    showTermArgs (t₁ ∷ t₂ ∷ ts) = showTerm t₁ ++ " , " ++ showTermArgs (t₂ ∷ ts)

  showSubst : ∀ {m n} → Subst m n → String
  showSubst s = "{" ++ showSubst' s ++ "}"
    where
    showFor : ∀ {n} (x : Fin (suc n)) (t : Term n) → String
    showFor x t = "?" ++ showFin x ++ " → " ++ showTerm t

    showSubst' : ∀ {m n} → Subst m n → String
    showSubst' nil = ""
    showSubst' (snoc nil t x)
      = "?" ++ showFin x ++ " → " ++ showTerm t
    showSubst' (snoc (snoc s t₂ x₂) t₁ x₁)
      = showFor x₁ t₁ ++ " , " ++ showSubst' (snoc s t₂ x₂)
