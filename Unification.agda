open import Prelude hiding (_++_)
open import Function using (_∘_)
open import Data.Fin using (raise)
open import Data.String using (String)
open import Data.Vec using (Vec; []; _∷_) renaming (map to vmap)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (cong)

module Unification (Op : Set) (arity : Op → ℕ) (equal? : (x y : Op) → Either (x ≡ y) (x ≢ y)) where

  data Term (n : ℕ) : Set where
    Var : Fin n → Term n
    Con : (x : Op) → (xs : Vec (Term n) (arity x)) → Term n

  data Subst : (n m : ℕ) → Set where
    Nil  : {n : ℕ} → Subst n n
    Cons : {n m : ℕ} → Fin (suc m) → Term m → Subst m n → Subst (suc m) n

  mutual
    replace : {n m : ℕ} → (Fin n → Term m) → Term n → Term m
    replace f (Var i) = f i
    replace f (Con x xs) = Con x (replaceChildren f xs)

    replaceChildren : {n m k : ℕ} → (Fin n → Term m) → Vec (Term n) k → Vec (Term m) k
    replaceChildren f [] = []
    replaceChildren f (x ∷ xs) = replace f x ∷ (replaceChildren f xs)

  replaceCorrect : ∀ {n} {T : Term n} → replace Var T ≡ T
  replaceCorrect {n} {Var x}    = refl
  replaceCorrect {n} {Con x xs} = cong (Con x) {!vmap !}
    where
    ≟-Fin : ∀ {n} → Decidable {A = Fin n} _≡_
    ≟-Fin  Fz     Fz    = yes refl
    ≟-Fin  Fz    (Fs y) = no (λ ())
    ≟-Fin (Fs x)  Fz    = no (λ ())
    ≟-Fin (Fs x) (Fs y) with ≟-Fin x y
    ≟-Fin (Fs x) (Fs y) | yes p = yes (cong Fs p)
    ≟-Fin (Fs x) (Fs y) | no ¬p = no {!!}

    mutual
      ≟-Term : ∀ {n} → Decidable {A = Term n} _≡_
      ≟-Term (Var x) (Var y) with ≟-Fin x y
      ≟-Term (Var x) (Var y) | yes p = yes (cong Var p)
      ≟-Term (Var x) (Var y) | no ¬p = no {!!}

      ≟-Term (Var x) (Con g ys)      = no (λ ())
      ≟-Term (Con f xs) (Var y)      = no (λ ())

      ≟-Term (Con  f  xs) (Con g ys) with equal? f g
      ≟-Term (Con .f  xs) (Con f ys) | Inl refl with ≟-Vec xs ys
      ≟-Term (Con .f .xs) (Con f xs) | Inl refl | yes refl = yes refl
      ≟-Term (Con .f  xs) (Con f ys) | Inl refl | no ¬p = no {!!}
      ≟-Term (Con  f  xs) (Con g ys) | Inr ¬p = no {!!}

      ≟-Vec : ∀ {n k} → Decidable {A = Vec (Term n) k} _≡_
      ≟-Vec [] [] = yes refl
      ≟-Vec (x₀ ∷ v₀) (x₁ ∷ v₁) = {!!}

  empty : {n : ℕ} → ∃ (Subst n)
  empty {n} = n , Nil

  _⋄_ : {k n m : ℕ} → (Fin m → Term n) → (Fin k → Term m) → Fin k → Term n
  _⋄_ f g i = replace f (g i)

  mutual
    check : {n : ℕ} → (i : Fin (suc n)) → (t : Term (suc n)) → Maybe (Term n)
    check i (Var j) = Var <$> thick i j
    check i (Con x xs) = Con x <$> checkChildren i xs

    checkChildren : {n k : ℕ} → (i : Fin (suc n)) → (ts : Vec (Term (suc n)) k) → Maybe (Vec (Term n) k)
    checkChildren i [] = Just []
    checkChildren i (x ∷ xs) = check i x >>= λ t →
                               checkChildren i xs >>= λ ts →
                               Just (t ∷ ts)


  _for_ : {n : ℕ} → (t : Term n) → (i j : Fin (suc n)) → Term n
  _for_ t' i j with thick i j
  _for_ t' i j | Nothing = t'
  _for_ t' i j | Just x = Var x

  apply : {n m : ℕ} → Subst n m → Fin n → Term m
  apply Nil = Var
  apply (Cons i t subst) = apply subst ⋄ (t for i)

  _++_ : {n m k : ℕ} → Subst n m → Subst m k → Subst n k
  Nil ++ subst' = subst'
  Cons i t subst ++ subst' = Cons i t (subst ++ subst')

  flexRigid : {n : ℕ} → Fin n → Term n → Maybe (∃ (Subst n))
  flexRigid {zero} () t
  flexRigid {suc k} i t with check i t
  flexRigid {suc k} i t | Nothing = Nothing
  flexRigid {suc k} i t | Just x  = Just (k , (Cons i x Nil))

  flexFlex : {n : ℕ} → (i j : Fin n) → ∃ (Subst n)
  flexFlex {zero} () j
  flexFlex {suc k} i j with thick i j
  flexFlex {suc k} i j | Nothing = ((suc k) , Nil)
  flexFlex {suc k} i j | Just x  = (k , Cons i (Var x) Nil)

  mutual
    unifyAcc : {m : ℕ} → (s t : Term m) → ∃ (Subst m) → Maybe (∃ (Subst m))
    unifyAcc (Con  x xs) (Con y ys) acc with equal? x y
    unifyAcc (Con .y xs) (Con y ys) acc | Inl refl = unifyChildren xs ys acc
    unifyAcc (Con  x xs) (Con y ys) acc | Inr y' = Nothing
    unifyAcc (Var i) (Var j) (k , Nil) = Just (flexFlex i j)
    unifyAcc (Var i) t (k , Nil) = flexRigid i t
    unifyAcc t (Var j) (k , Nil) = flexRigid j t
    unifyAcc s t (k , Cons i t' subst) =
      (λ s → (witness s) , (Cons i t' (proof s)))
        <$> unifyAcc (replace (t' for i) s) (replace (t' for i) t) (k , subst)

    unifyChildren : {n k : ℕ} → (xs ys : Vec (Term n) k) → ∃ (Subst n) → Maybe (∃ (Subst n))
    unifyChildren [] [] acc = Just acc
    unifyChildren (x ∷ xs) (y ∷ ys) acc = unifyAcc x y acc >>= unifyChildren xs ys

  unify  : {m : ℕ} → (s t : Term m) → Maybe (∃ (Subst m))
  unify {m} s t = unifyAcc s t (m , Nil)
