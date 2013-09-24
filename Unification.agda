open import Function using (_∘_)
open import Category.Functor
open import Category.Monad
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Props as FinProps using ()
open import Data.Maybe as Maybe using (Maybe; maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail)
open import Data.Vec.Equality as VecEq
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary as Bin using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; cong; inspect; Reveal_is_; [_])

module Unification (Symbol : Set) (arity : Symbol → ℕ) (decEqSym : Decidable {A = Symbol} _≡_) where

open RawFunctor {{...}}
open RawMonad {{...}} hiding (_<$>_)
open Bin.DecSetoid {{...}} using (_≟_)

private maybeFunctor = Maybe.functor
private maybeMonad = Maybe.monad
private finDecSetoid : ∀ {n} → DecSetoid _ _
        finDecSetoid {n} = FinProps.decSetoid n

-- defining terms

data Term (n : ℕ) : Set where
  Var : Fin n → Term n
  Con : (s : Symbol) → (ts : Vec (Term n) (arity s)) → Term n

-- defining decidable equality on terms
mutual
  decEqTerm : ∀ {n} → Decidable {A = Term n} _≡_
  decEqTerm (Var  x₁) (Var x₂) with x₁ ≟ x₂
  decEqTerm (Var .x₂) (Var x₂) | yes refl = yes refl
  decEqTerm (Var  x₁) (Var x₂) | no x₁≢x₂ = no (x₁≢x₂ ∘ lem)
    where
    lem : ∀ {n} {x y : Fin n} → Var x ≡ Var y → x ≡ y
    lem {n} {x} {.x} refl = refl
  decEqTerm (Var _) (Con _ _) = no (λ ())
  decEqTerm (Con _ _) (Var _) = no (λ ())
  decEqTerm (Con s₁ ts₁) (Con  s₂ ts₂) with decEqSym s₁  s₂
  decEqTerm (Con s₁ ts₁) (Con  s₂ ts₂) | no s₁≢s₂ = no (s₁≢s₂ ∘ lem)
    where
    lem : ∀ {n} {x y} {xs : Vec (Term n) _} {ys : Vec (Term n) _} → Con x xs ≡ Con y ys → x ≡ y
    lem {n} {x} {.x} refl = refl
  decEqTerm (Con s₁ ts₁) (Con .s₁ ts₂) | yes refl with decEqVecTerm ts₁ ts₂
  decEqTerm (Con s₁ ts₁) (Con .s₁ ts₂) | yes refl | no ts₁≢ts₂ = no (ts₁≢ts₂ ∘ lem)
    where
    lem : ∀ {n} {x} {xs ys : Vec (Term n) _} → Con x xs ≡ Con x ys → xs ≡ ys
    lem {n} {x} {xs} {.xs} refl = refl
  decEqTerm (Con s₁ .ts₂) (Con .s₁ ts₂) | yes refl | yes refl = yes refl

  decEqVecTerm : ∀ {n k} → Decidable {A = Vec (Term n) k} _≡_
  decEqVecTerm [] [] = yes refl
  decEqVecTerm (x ∷ xs) ( y ∷  ys) with decEqTerm x y | decEqVecTerm xs ys
  decEqVecTerm (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
  decEqVecTerm (x ∷ xs) ( y ∷  ys) | yes _    | no xs≢ys = no (xs≢ys ∘ cong tail)
  decEqVecTerm (x ∷ xs) ( y ∷  ys) | no x≢y   | _        = no (x≢y ∘ cong head)

termDecSetoid : ∀ {n} → DecSetoid _ _
termDecSetoid {n} = PropEq.decSetoid (decEqTerm {n})

-- defining replacement function (written _◂ in McBride, 2003)

mutual
  replace : ∀ {n m} → (Fin n → Term m) → Term n → Term m
  replace f (Var i)    = f i
  replace f (Con s ts) = Con s (replaceChildren f ts)

  replaceChildren : ∀ {n m k} → (Fin n → Term m) → Vec (Term n) k → Vec (Term m) k
  replaceChildren f []       = []
  replaceChildren f (x ∷ xs) = replace f x ∷ (replaceChildren f xs)

-- defining substitution/replacement composition

_◇_ : ∀ {m n l} (f : Fin m → Term n) (g : Fin l → Term m) → Fin l → Term n
_◇_ f g = replace f ∘ g

-- defining thick and thin

thin : {n : ℕ} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin  zero    y      = suc y
thin (suc x)  zero   = zero
thin (suc x) (suc y) = suc (thin x y)

thick : {n : ℕ} -> (x y : Fin (suc n)) -> Maybe (Fin n)
thick          zero    zero   = nothing
thick          zero   (suc y) = just y
thick {zero}  (suc ()) _
thick {suc n} (suc x)  zero   = just zero
thick {suc n} (suc x) (suc y) = suc <$> thick x y

-- defining an occurs check (**check** in McBride, 2003)

mutual
  check : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) → Maybe (Term n)
  check x₁ (Var x₂) = Var <$> thick x₁ x₂
  check x₁ (Con s ts) = Con s <$> checkChildren x₁ ts


  checkChildren : ∀ {n k} (x : Fin (suc n)) (ts : Vec (Term (suc n)) k) → Maybe (Vec (Term n) k)
  checkChildren x₁ [] = just []
  checkChildren x₁ (t ∷ ts) = check x₁ t >>= λ t' →
                              checkChildren x₁ ts >>= λ ts' →
                              return (t' ∷ ts')

-- defining substitutions (AList in McBride, 2003)

data Subst : ℕ → ℕ → Set where
  nil  : ∀ {n}   → Subst n n
  snoc : ∀ {m n} → (s : Subst m n) → (t : Term m) → (x : Fin (suc m)) → Subst (suc m) n

-- defining function substituting t for x (**for** in McBride, 2003)

_for_ : ∀ {n} (t : Term n) (x : Fin (suc n)) → Fin (suc n) → Term n
_for_ t x y with thick x y
_for_ t x y | just y' = Var y'
_for_ t x y | nothing = t


-- defining substitution application (**sub** in McBride, 2003)

apply : ∀ {m n} → Subst m n → Fin m → Term n
apply nil = Var
apply (snoc s t x) = (apply s) ◇ (t for x)

-- defining substitution concatination

_++_ : ∀ {l m n} → Subst m n → Subst l m → Subst l n
s₁ ++ nil = s₁
s₁ ++ (snoc s₂ t x) = snoc (s₁ ++ s₂) t x
