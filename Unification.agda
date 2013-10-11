open import Function using (_∘_)
open import Category.Functor
open import Category.Monad
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Props as FinProps using ()
open import Data.Maybe as Maybe using (Maybe; maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail)
open import Data.Vec.Equality as VecEq
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; inspect; [_])

module Unification (Name : ℕ → Set) (decEqName : ∀ {k} (x y : Name k) → Dec (x ≡ y)) where

  open RawFunctor {{...}}
  open RawMonad {{...}} hiding (_<$>_)
  open DecSetoid {{...}} using (_≟_)

  private maybeFunctor = Maybe.functor
  private maybeMonad   = Maybe.monad
  private natDecSetoid = PropEq.decSetoid Nat._≟_
  private finDecSetoid : ∀ {n} → DecSetoid _ _
          finDecSetoid {n} = FinProps.decSetoid n
  private nameDecSetoid : ∀ {k} → DecSetoid _ _
          nameDecSetoid {k} = PropEq.decSetoid (decEqName {k})

  -- defining terms
  data Term (n : ℕ) : Set where
    var : Fin n → Term n
    con : ∀ {k} (s : Name k) → (ts : Vec (Term n) k) → Term n

  -- defining decidable equality on terms
  mutual
    decEqTerm : ∀ {n} → (t₁ t₂ : Term n) → Dec (t₁ ≡ t₂)
    decEqTerm (var  x₁) (var x₂) with x₁ ≟ x₂
    decEqTerm (var .x₂) (var x₂) | yes refl = yes refl
    decEqTerm (var  x₁) (var x₂) | no x₁≢x₂ = no (x₁≢x₂ ∘ elim)
      where
      elim : ∀ {n} {x y : Fin n}
           → var x ≡ var y → x ≡ y
      elim {n} {x} {.x} refl = refl
    decEqTerm (var _)   (con _ _) = no (λ ())
    decEqTerm (con _ _) (var _)   = no (λ ())
    decEqTerm (con {k₁} s₁ ts₁) (con {k₂} s₂ ts₂) with k₁ ≟ k₂
    decEqTerm (con {k₁} s₁ ts₁) (con {k₂} s₂ ts₂) | no k₁≢k₂ = no (k₁≢k₂ ∘ elim)
      where
      elim : ∀ {n k₁ k₂ s₁ s₂} {ts₁ : Vec (Term n) k₁} {ts₂ : Vec (Term n) k₂}
           → con {n} {k₁} s₁ ts₁ ≡ con {n} {k₂} s₂ ts₂ → k₁ ≡ k₂
      elim {n} {k} {.k} refl = refl
    decEqTerm (con {.k} s₁ ts₁) (con { k} s₂ ts₂) | yes refl with s₁ ≟ s₂
    decEqTerm (con s₁ ts₁) (con s₂ ts₂) | yes refl | no s₁≢s₂ = no (s₁≢s₂ ∘ elim)
      where
      elim : ∀ {n k s₁ s₂} {ts₁ ts₂ : Vec (Term n) k}
           → con s₁ ts₁ ≡ con s₂ ts₂ → s₁ ≡ s₂
      elim {n} {k} {s} {.s} refl = refl
    decEqTerm (con .s ts₁) (con s ts₂) | yes refl | yes refl with decEqVecTerm ts₁ ts₂
    decEqTerm (con .s ts₁) (con s ts₂) | yes refl | yes refl | no ts₁≢ts₂  = no (ts₁≢ts₂ ∘ elim)
      where
      elim : ∀ {n k s} {ts₁ ts₂ : Vec (Term n) k}
           → con s ts₁ ≡ con s ts₂ → ts₁ ≡ ts₂
      elim {n} {k} {s} {ts} {.ts} refl = refl
    decEqTerm (con .s .ts) (con s ts) | yes refl | yes refl | yes refl = yes refl

    decEqVecTerm : ∀ {n k} → (xs ys : Vec (Term n) k) → Dec (xs ≡ ys)
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
    replace f (var i)  = f i
    replace f (con s ts) = con s (replaceChildren f ts)

    replaceChildren : ∀ {n m k} → (Fin n → Term m) → Vec (Term n) k → Vec (Term m) k
    replaceChildren f []       = []
    replaceChildren f (x ∷ xs) = replace f x ∷ (replaceChildren f xs)


  -- defining replacement composition

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


  -- | defining an occurs check (**check** in McBride, 2003)
  mutual
    check : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) → Maybe (Term n)
    check x₁ (var x₂)   = var <$> thick x₁ x₂
    check x₁ (con s ts) = con s <$> checkChildren x₁ ts

    checkChildren : ∀ {n k} (x : Fin (suc n)) (ts : Vec (Term (suc n)) k) → Maybe (Vec (Term n) k)
    checkChildren x₁ [] = just []
    checkChildren x₁ (t ∷ ts) = check x₁ t >>= λ t' →
      checkChildren x₁ ts >>= λ ts' → return (t' ∷ ts')


  -- | datatype for substitutions (AList in McBride, 2003)
  data Subst : ℕ → ℕ → Set where
    nil  : ∀ {n}   → Subst n n
    snoc : ∀ {m n} → (s : Subst m n) → (t : Term m) → (x : Fin (suc m)) → Subst (suc m) n


  -- | substitutes t for x (**for** in McBride, 2003)
  _for_ : ∀ {n} (t : Term n) (x : Fin (suc n)) → Fin (suc n) → Term n
  _for_ t x y with thick x y
  _for_ t x y | just y' = var y'
  _for_ t x y | nothing = t


  -- | substitution application (**sub** in McBride, 2003)
  apply : ∀ {m n} → Subst m n → Fin m → Term n
  apply nil = var
  apply (snoc s t x) = (apply s) ◇ (t for x)


  -- | composes two substitutions
  _++_ : ∀ {l m n} → Subst m n → Subst l m → Subst l n
  s₁ ++ nil = s₁
  s₁ ++ (snoc s₂ t x) = snoc (s₁ ++ s₂) t x


  flexRigid : ∀ {n} → Fin n → Term n → Maybe (∃ (Subst n))
  flexRigid {zero} () t
  flexRigid {suc n} x t with check x t
  flexRigid {suc n} x t | nothing = nothing
  flexRigid {suc n} x t | just t' = just (n , snoc nil t' x)

  flexFlex : ∀ {n} → (x y : Fin n) → ∃ (Subst n)
  flexFlex {zero} () j
  flexFlex {suc n} x y with thick x y
  flexFlex {suc n} x y | nothing = (suc n , nil)
  flexFlex {suc n} x y | just  z = (n , snoc nil (var z) x)

  mutual
    unifyAcc : ∀ {m} → (t₁ t₂ : Term m) → ∃ (Subst m) → Maybe (∃ (Subst m))
    unifyAcc (con {k₁} s₁ ts₁) (con {k₂} s₂ ts₂) acc with k₁ ≟ k₂
    unifyAcc (con {k₁} s₁ ts₁) (con {k₂} s₂ ts₂) acc | no k₁≢k₂ = nothing
    unifyAcc (con { k} s₁ ts₁) (con {.k} s₂ ts₂) acc | yes refl with s₁ ≟ s₂
    unifyAcc (con { k} s₁ ts₁) (con {.k} s₂ ts₂) acc | yes refl | no s₁≢s₂ = nothing
    unifyAcc (con { k} .s ts₁) (con {.k}  s ts₂) acc | yes refl | yes refl = unifyAccChildren ts₁ ts₂ acc
    unifyAcc (var x₁) (var x₂) (n , nil) = just (flexFlex x₁ x₂)
    unifyAcc (var x₁) t₂       (n , nil) = flexRigid x₁ t₂
    unifyAcc t₁       (var x₂) (n , nil) = flexRigid x₂ t₁
    unifyAcc t₁ t₂ (n , snoc s t' x) =
      ( λ s → proj₁ s , snoc (proj₂ s) t' x )
        <$> unifyAcc (replace (t' for x) t₁) (replace (t' for x) t₂) (n , s)

    unifyAccChildren : ∀ {n k} → (ts₁ ts₂ : Vec (Term n) k) → ∃ (Subst n) → Maybe (∃ (Subst n))
    unifyAccChildren []         []         acc = just acc
    unifyAccChildren (t₁ ∷ ts₁) (t₂ ∷ ts₂) acc = unifyAcc t₁ t₂ acc >>= unifyAccChildren ts₁ ts₂

  unify : ∀ {m} → (t₁ t₂ : Term m) → Maybe (∃ (Subst m))
  unify {m} t₁ t₂ = unifyAcc t₁ t₂ (m , nil)

  -- * concept of compactness for terms
