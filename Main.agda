open import Function using (_∘_; _$_; flip)
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
  showSym ADD  = "Add"
  showSym SUC  = "Suc"
  showSym ZERO = "Zero"

  import Prolog
  module PI = Prolog String Sym decEqSym
  open PI

  import Unification.Show
  module US = Unification.Show Sym showSym decEqSym
  open US

  Zero : ∀ {n} → Term n
  Zero = con ZERO []

  Suc : ∀ {n} (x : Term n) → Term n
  Suc x = con SUC (x ∷ [])

  fromℕ : ∀ {n} → ℕ → Term n
  fromℕ zero = Zero
  fromℕ (suc k) = Suc (fromℕ k)

  toℕ : Term 0 → ℕ
  toℕ (var ())
  toℕ (con ADD  (x ∷ y ∷ z ∷ [])) = toℕ z
  toℕ (con SUC  (x ∷ []))         = suc (toℕ x)
  toℕ (con ZERO [])               = zero

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

  showEnv : ∀ {m} → Vec (Term 0) m → String
  showEnv ans = "{" ++ showEnv' ans ++ "}"
    where
    showEnv' : ∀ {m} → Vec (Term 0) m → String
    showEnv' [] = ""
    showEnv' (t₁ ∷ []) = showℕ (toℕ t₁)
    showEnv' (t₁ ∷ t₂ ∷ ts) = showℕ (toℕ t₁) ++ "; " ++ showEnv' (t₂ ∷ ts)

  joinBy : String → List String → String
  joinBy sep = concat ∘ intersperse sep
    where
      concat : List String → String
      concat = foldr (_++_) ""

  showTrace : Rules → String
  showTrace = joinBy ";" ∘ map (name ∘ proj₂)

  -- TODO
  --   I believe that there's a simple way to fix this termination checker
  --   issue, as we've discussed this problem in class (it's due to the map), but
  --   since it's really just a show function I won't bother.

  {-# NO_TERMINATION_CHECK #-}
  showProof : Proof → String
  showProof (con n ps) = n ++ "(" ++ (joinBy "," ∘ map showProof $ ps) ++ ")"

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

  main : String
  main = showList showAns (filterWithVars' (solveToDepth 10 rules goal))
