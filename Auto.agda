open import Function using (_∘_)
open import Data.Fin using (Fin; Fin′; suc; zero; toℕ)
open import Data.Nat as Nat using (ℕ; suc; zero; _⊔_; decTotalOrder)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃₂; Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to smap)
open import Data.List using (List; _∷_; []; concatMap)
open import Data.Vec using (Vec; _∷_; [])
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

  open import Prolog PName _≟-PName_ renaming (Term to PTerm)

  -- implement a small example of what the auto tactic should be able to do,
  -- in order to guide the conversion work below.

  exampleGoal : ℕ
  exampleGoal = quoteGoal g in {!!}

  -- implement functions to convert Agda terms to Prolog terms, and ℕ-indexed
  -- variables to Fin-indexed variables.

  -- TODO: implement several injection functions to inject finite terms into the maximum

  open DecTotalOrder {{...}}
  private natDecTotalOrder = Nat.decTotalOrder

  break : ∀ n (n₁ : Fin n) → Fin n → Σ (Fin n) (λ n₂ → Fin′ n₁ ⊎ Fin′ n₂)
  break .(suc n) (zero {n})     x      = {!!}
  break .(suc n) (suc  {n} n₁)  zero   = {!!}
  break .(suc n) (suc  {n} n₁) (suc x) = {!!}

  mutual
    toPTerm : ATerm → ∃ (λ n → PTerm n)
    toPTerm (var x args) = {!!}
    toPTerm (con c args) = {!!}
    toPTerm (def f args) = {!!}
    toPTerm (lam v t)    = {!!}
    toPTerm (pi t₁ t₂)   = {!!}
    toPTerm (sort x)     = {!!}
    toPTerm unknown      = {!!}

    toPTerms : List (Arg ATerm) → ∃₂ (λ n k → Vec (PTerm n) k)
    toPTerms [] = 0 , 0 , []
    toPTerms (arg visible _ a ∷ as)
        with toPTerm a | toPTerms as
    ... | n₁ , p | n₂ , k , ps = n₁ ⊔ n₂ , suc k , {!!}
    toPTerms (arg _       _ a ∷ as) = toPTerms as
