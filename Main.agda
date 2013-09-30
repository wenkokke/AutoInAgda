open import Function using (_∘_)
open import Coinduction
open import IO
open import IO.Primitive as Prim using ()
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; _,_)
open import Data.String
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

module Main where

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
    Add₀ = 1 , Add Zero x x :- []
      where x = var zero
    Add₁ = 3 , Add (Suc x) y (Suc z) :- (Add x y z ∷ [])
      where x = var zero
            y = var (suc zero)
            z = var (suc (suc zero))

  goal : Goal 1
  goal = Add (Suc Zero) (Suc (Suc Zero)) (var zero)

  main : String
  main with solve rules goal
  main | zero , st = "no variables"
  main | suc n , st = ppsub ss ++ " | " ++ ppans (ans ss)
    where
    ss = toDepth 10 (dfs st)

    ans : List (∃ (Subst (suc n))) → List (∃ Term)
    ans [] = []
    ans ((m , sub) ∷ subs) = (m , (apply sub zero)) ∷ ans subs

    ppans : List (∃ Term) → String
    ppans [] = ""
    ppans ((m , t) ∷ ts) = showTerm t ++ ";" ++ ppans ts

    ppsub : List (∃ (Subst (suc n))) → String
    ppsub [] = ""
    ppsub ((m , s) ∷ []) = showSubst s
    ppsub ((m , s₁) ∷ s₂ ∷ ss) = showSubst s₁ ++ " ; " ++ ppsub (s₂ ∷ ss)
