open import Level using (suc; zero)
open import Function using (_∘_; flip)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Reflection renaming (Term to ATerm; Name to AName; _≟-Name_ to _≟-AName_)

-- import basic connectives of propositional logic

open import Function using () renaming (_$_ to →-elim)
open import Function.Equivalence using (_⇔_) renaming (equivalence to ⇔-intro)
open import Data.Unit using (⊤) renaming (tt to ⊤-intro)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Product using () renaming (_×_ to _∧_; _,_ to ∧-intro; proj₁ to ∧-elim₁; proj₂ to ∧-elim₂)
open import Data.Sum using () renaming (_⊎_ to _∨_; inj₁ to ∨-intro₁; inj₂ to ∨-intro₂; [_,_] to ∨-elim)

module Auto where

  example₁ : {A B C : Set} → (A ∧ B → C) ⇔ (A → B → C)
  example₁ = ⇔-intro (λ h a b → h (∧-intro a b)) (λ h a∧b → h (∧-elim₁ a∧b) (∧-elim₂ a∧b))

  -- extend Agda names to carry an arity and extend decidable equality to
  -- work on them; then load the Prolog package using these names as identifiers.

  data PName : ℕ → Set where
    pname : (n : AName) (k : ℕ) → PName k

  _≟-PName_ : ∀ {k} (x y : PName k) → Dec (x ≡ y)
  _≟-PName_ {k} (pname x .k) (pname  y .k) with x ≟-AName y
  _≟-PName_ {k} (pname x .k) (pname .x .k) | yes refl = yes refl
  _≟-PName_ {k} (pname x .k) (pname  y .k) | no  x≢y  = no (x≢y ∘ cong elim)
    where
    elim : ∀ {k} → PName k → AName
    elim {k} (pname n .k) = n

  open import Prolog AName PName _≟-PName_ renaming (Term to PTerm)

  -- implement a small example of what the auto tactic should be able to do,
  -- in order to guide the conversion work below.

  -- implement functions to convert Agda terms to Prolog terms, and ℕ-indexed
  -- variables to Fin-indexed variables.
