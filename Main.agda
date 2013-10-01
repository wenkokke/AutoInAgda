open import Function using (_∘_)
open import Coinduction
open import Category.Monad
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_) renaming (map to vmap)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; _,_)
open import Data.String
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

module Main where

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
  showSym ADD  = "+"
  showSym SUC  = "S"
  showSym ZERO = "0"

  import Prolog
  module PI = Prolog Sym decEqSym
  open PI

  import Unification.Show
  module US = Unification.Show Sym showSym decEqSym
  open US

  Zero : ∀ {n} → Term n
  Zero = con ZERO []

  Suc : ∀ {n} (x : Term n) → Term n
  Suc x = con SUC (x ∷ [])

  Add : ∀ {n} (x y z : Term n) → Term n
  Add x y z = con ADD (x ∷ y ∷ z ∷ [])

  rules : Rules
  rules = Add₀ ∷ Add₁ ∷ []
    where
    Add₀ = 1 , Add Zero x₀ x₀ :- []
      where x₀ = var zero
    Add₁ = 3 , Add (Suc x₀) x₁ (Suc x₂) :- (Add x₀ x₁ x₂ ∷ [])
      where x₀ = var zero
            x₁ = var (suc zero)
            x₂ = var (suc (suc zero))

  goal : Goal 2
  goal = Add x₀ x₁ (Suc (Suc Zero))
    where x₀ = var zero
          x₁ = var (suc zero)

  mutual
    noVars : ∀ {n} → Term n → Maybe (Term 0)
    noVars (var x)    = nothing
    noVars (con s ts) = con s <$> noVarsChildren ts

    noVarsChildren : ∀ {n k} → Vec (Term n) k → Maybe (Vec (Term 0) k)
    noVarsChildren [] = just []
    noVarsChildren (t ∷ ts) = noVars t >>= λ t' →
                              noVarsChildren ts >>= λ ts' →
                              mreturn (t' ∷ ts')

    toℕ : Term 0 → ℕ
    toℕ (var ())
    toℕ (con ZERO []) = zero
    toℕ (con SUC (x ∷ [])) = suc (toℕ x)
    toℕ (con ADD (x ∷ y ∷ z ∷ [])) = toℕ z

  showAns : ∀ {m} → Vec (∃ Term) m → String
  showAns ans = "{" ++ showAns' ans ++ "}"
    where
    showTerm∃ : ∃ Term → String
    showTerm∃ (n , t) with noVars t
    ... | nothing = showTerm t
    ... | just t' = showℕ (toℕ t')

    showAns' : ∀ {m} → Vec (∃ Term) m → String
    showAns' [] = ""
    showAns' (t₁ ∷ []) = showTerm∃ t₁
    showAns' (t₁ ∷ t₂ ∷ ts) = showTerm∃ t₁ ++ "; " ++ showAns' (t₂ ∷ ts)


  showList : ∀ {ℓ} {A : Set ℓ} (show : A → String) → List A → String
  showList show [] = ""
  showList show (x ∷ []) = show x
  showList show (x ∷ y ∷ xs) = show x ++ " , " ++ showList show (y ∷ xs)

  main : String
  main = showList showAns (solveToDepth 10 rules goal)
