open import Function using (_∘_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.List using (List; _∷_; []; concatMap)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Reflection renaming (Term to ATerm; Name to AName; _≟-Name_ to _≟-AName_)

module Auto where

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

  open import Prolog PName _≟-PName_
