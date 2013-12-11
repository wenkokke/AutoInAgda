open import Function using (_∘_; _$_; flip; id)
open import Coinduction
open import Category.Monad
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Vec using (Vec; []; _∷_; toList) renaming (map to vmap)
open import Data.List using (List; []; _∷_; intersperse; map; foldr; foldl; reverse)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

module Prolog.Example where

  open RawMonad {{...}} renaming (return to mreturn)
  private maybeMonad = Maybe.monad

  data Sym : ℕ → Set where
    ADD  : Sym 3
    SUC  : Sym 1
    ZERO : Sym 0

  decEqSym : ∀ {k} (f g : Sym k) → Dec (f ≡ g)
  decEqSym ADD  ADD  = yes refl
  decEqSym SUC  SUC  = yes refl
  decEqSym ZERO ZERO = yes refl

  showSym : ∀ {k} (s : Sym k) → String
  showSym ADD  = "Add"
  showSym SUC  = "Suc"
  showSym ZERO = "Zero"

  open import Prolog String Sym decEqSym
  open import Prolog.Show String id Sym showSym decEqSym

  Zero : ∀ {n} → Term n
  Zero = con ZERO []

  Suc : ∀ {n} (x : Term n) → Term n
  Suc x = con SUC (x ∷ [])

  fromℕ : ∀ {n} → ℕ → Term n
  fromℕ zero = Zero
  fromℕ (suc k) = Suc (fromℕ k)

  Add : ∀ {n} (x y z : Term n) → Term n
  Add x y z = con ADD (x ∷ y ∷ z ∷ [])

  rules : Rules
  rules = Add₁ ∷ Add₀ ∷ []
    where
      Add₀ = 1 , rule "Add₀" (Add Zero x₀ x₀) []
        where x₀ = var zero
      Add₁ = 3 , rule "Add₁" (Add (Suc x₀) x₁ (Suc x₂)) (Add x₀ x₁ x₂ ∷ [])
        where x₀ = var zero
              x₁ = var (suc zero)
              x₂ = var (suc (suc zero))

  goal : Goal 2
  goal = Add x₀ x₁ (fromℕ 4)
    where x₀ = var zero
          x₁ = var (suc zero)

  main : String
  main = showList showAns (filterWithVars (solveToDepth 10 rules goal))
