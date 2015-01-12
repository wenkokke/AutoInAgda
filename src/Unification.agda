open import Function using (_∘_)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Fin.Properties as FinProps renaming (_≟_ to _≟-Fin_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; monad)
open import Data.List as List using (List; _∷_; []; monad)
open import Data.List.Properties as ListProps renaming (∷-injective to ∷-inj)
open import Data.Product as Prod using (∃; _×_; _,_; proj₁; proj₂)
open import Category.Monad using (module RawMonad)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; cong₂)

module Unification
  (Name : Set) (_≟-Name_ : (x y : Name) → Dec (x ≡ y))
  (Literal : Set) (_≟-Literal_ : (x y : Literal) → Dec (x ≡ y))
  where

  open RawMonad {{...}} using (_<$>_; _>>=_; return)

  private
    instance
      MaybeMonad = Maybe.monad

  data Term (n : ℕ) : Set where
    var : (x : Fin n) → Term n
    con : (s : Name) (ts : List (Term n)) → Term n
    lit : (l : Literal) → Term n
--  ext : (x : Fin (suc n)) (t : Term (suc n)) → Term n

  var-inj : ∀ {n x₁ x₂} → var {n} x₁ ≡ var {n} x₂ → x₁ ≡ x₂
  var-inj refl = refl

  con-inj : ∀ {n s₁ s₂ ts₁ ts₂} → con {n} s₁ ts₁ ≡ con {n} s₂ ts₂ → s₁ ≡ s₂ × ts₁ ≡ ts₂
  con-inj refl = (refl , refl)

  lit-inj : ∀ {n x₁ x₂} → lit {n} x₁ ≡ lit {n} x₂ → x₁ ≡ x₂
  lit-inj refl = refl

--ext-inj : ∀ {n x₁ x₂ t₁ t₂} → ext {n} x₁ t₁ ≡ ext {n} x₂ t₂ → x₁ ≡ x₂ × t₁ ≡ t₂
--ext-inj refl = refl , refl

  mutual
    _≟-Term_ : ∀ {n} → (t₁ t₂ : Term n) → Dec (t₁ ≡ t₂)
    _≟-Term_ (var _)  (lit _)   = no (λ ())
    _≟-Term_ (var _)  (con _ _) = no (λ ())
--  _≟-Term_ (var _)  (ext _ _) = no (λ ())
    _≟-Term_ (var x₁) (var x₂) with x₁ ≟-Fin x₂
    ... | yes x₁=x₂ = yes (cong var x₁=x₂)
    ... | no  x₁≠x₂ = no (x₁≠x₂ ∘ var-inj)
    _≟-Term_ (con _ _)    (var _)   = no (λ ())
    _≟-Term_ (con _ _)    (lit _)   = no (λ ())
--  _≟-Term_ (con _ _)    (ext _ _) = no (λ ())
    _≟-Term_ (con s₁ ts₁) (con s₂ ts₂) with s₁ ≟-Name s₂
    ... | no  s₁≠s₂ = no (s₁≠s₂ ∘ proj₁ ∘ con-inj)
    ... | yes s₁=s₂ rewrite s₁=s₂ with ts₁ ≟-Terms ts₂
    ... | no  ts₁≠ts₂ = no (ts₁≠ts₂ ∘ proj₂ ∘ con-inj)
    ... | yes ts₁=ts₂ = yes (cong (con s₂) ts₁=ts₂)
    _≟-Term_ (lit _)  (var _)   = no (λ ())
    _≟-Term_ (lit _)  (con _ _) = no (λ ())
--  _≟-Term_ (lit _)  (ext _ _) = no (λ ())
    _≟-Term_ (lit x₁) (lit x₂) with x₁ ≟-Literal x₂
    ... | yes x₁=x₂ = yes (cong lit x₁=x₂)
    ... | no  x₁≠x₂ = no (x₁≠x₂ ∘ lit-inj)
--  _≟-Term_ (ext _ _)   (var _)        = no (λ ())
--  _≟-Term_ (ext _ _)   (con _ _)      = no (λ ())
--  _≟-Term_ (ext _ _)   (lit _)        = no (λ ())
--  _≟-Term_ (ext x₁ t₁) (ext x₂ t₂) with x₁ ≟-Fin x₂
--  ... | no  x₁≠x₂ = no (x₁≠x₂ ∘ proj₁ ∘ ext-inj)
--  ... | yes x₁=x₂ rewrite x₁=x₂ with t₁ ≟-Term t₂
--  ... | no  t₁≠t₂ = no (t₁≠t₂ ∘ proj₂ ∘ ext-inj)
--  ... | yes t₁=t₂ = yes (cong (ext x₂) t₁=t₂)

    _≟-Terms_ : ∀ {n} (xs ys : List (Term n)) → Dec (xs ≡ ys)
    _≟-Terms_ [] [] = yes refl
    _≟-Terms_ [] (_  ∷ _) = no (λ ())
    _≟-Terms_ (_ ∷ _) [] = no (λ ())
    _≟-Terms_ (x ∷ xs) (y ∷ ys) with x ≟-Term y
    ... | no  x≠y = no (x≠y ∘ proj₁ ∘ ∷-inj)
    ... | yes x=y with xs ≟-Terms ys
    ... | no  xs≠ys = no (xs≠ys ∘ proj₂ ∘ ∷-inj)
    ... | yes xs=ys = yes (cong₂ _∷_ x=y xs=ys)

  
  -- defining thick and thin
  thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
  thin  zero    y      = suc y
  thin (suc x)  zero   = zero
  thin (suc x) (suc y) = suc (thin x y)

  thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
  thick          zero    zero   = nothing
  thick          zero   (suc y) = just y
  thick {zero}  (suc ()) _
  thick {suc n} (suc x)  zero   = just zero
  thick {suc n} (suc x) (suc y) = suc <$> thick x y

  -- defining replacement function (written _◂ in McBride, 2003)
  replace : ∀ {n m} → (Fin n → Term m) → Term n → Term m
  replace _ (lit l) = lit l
  replace f (var i) = f i
  replace f (con s ts) = con s (replaceChildren f ts)
    where
      replaceChildren : ∀ {n m} → (Fin n → Term m) → (List (Term n) → List (Term m))
      replaceChildren f []       = []
      replaceChildren f (x ∷ xs) = replace f x ∷ (replaceChildren f xs)

  -- defining replacement composition
  _◇_ : ∀ {m n l} (f : Fin m → Term n) (g : Fin l → Term m) → Fin l → Term n
  _◇_ f g = replace f ∘ g

  -- defining an occurs check (**check** in McBride, 2003)
  check : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) → Maybe (Term n)
  check _  (lit l)    = just (lit l)
  check x₁ (var x₂)   = var <$> thick x₁ x₂
  check x₁ (con s ts) = con s <$> checkChildren x₁ ts
    where
      checkChildren : ∀ {n} (x : Fin (suc n)) (ts : List (Term (suc n))) → Maybe (List (Term n))
      checkChildren x₁ [] = just []
      checkChildren x₁ (t ∷ ts) = check x₁ t >>= λ t' →
        checkChildren x₁ ts >>= λ ts' → return (t' ∷ ts')

  -- datatype for substitutions (AList in McBride, 2003)
  data Subst : ℕ → ℕ → Set where
    nil  : ∀ {n}   → Subst n n
    snoc : ∀ {m n} → (s : Subst m n) → (t : Term m) → (x : Fin (suc m)) → Subst (suc m) n

  -- substitutes t for x (**for** in McBride, 2003)
  _for_ : ∀ {n} (t : Term n) (x : Fin (suc n)) → Fin (suc n) → Term n
  _for_ t x y with thick x y
  _for_ t x y | just y' = var y'
  _for_ t x y | nothing = t

  -- substitution application (**sub** in McBride, 2003)
  apply : ∀ {m n} → Subst m n → Fin m → Term n
  apply nil = var
  apply (snoc s t x) = (apply s) ◇ (t for x)

  -- composes two substitutions
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

  -- TODO ask Wouter/Ulf about problems with new notation...
  -- why are naturals represented as literals in the agda abstract syntax?
  -- for floats, chars and strings it makes sense since they HAVE NO agda
  -- representation
  mutual
    unifyAcc : ∀ {m} → (t₁ t₂ : Term m) → ∃ (Subst m) → Maybe (∃ (Subst m))
    unifyAcc (lit x₁) (lit x₂) (n , nil) with x₁ ≟-Literal x₂
    ... | yes x₁=x₂ rewrite x₁=x₂ = just (n , nil)
    ... | no  x₁≠x₂ = nothing
    unifyAcc (con s ts) (lit x) (n , nil) = nothing
    unifyAcc (lit x) (con s ts) (n , nil) = nothing
    unifyAcc (con s₁ ts₁) (con  s₂ ts₂) acc with s₁ ≟-Name s₂
    ... | yes s₁=s₂ rewrite s₁=s₂ = unifyAccChildren ts₁ ts₂ acc
    ... | no  s₁≠s₂ = nothing
    unifyAcc (var x₁) (var x₂) (n , nil) = just (flexFlex x₁ x₂)
    unifyAcc t (var x) (n , nil) = flexRigid x t
    unifyAcc (var x) t (n , nil) = flexRigid x t
    unifyAcc t₁ t₂ (n , snoc s t′ x) =
      ( λ s → proj₁ s , snoc (proj₂ s) t′ x )
        <$> unifyAcc (replace (t′ for x) t₁) (replace (t′ for x) t₂) (n , s)

    unifyAccChildren : ∀ {n} → (ts₁ ts₂ : List (Term n)) → ∃ (Subst n) → Maybe (∃ (Subst n))
    unifyAccChildren []         []       acc = just acc
    unifyAccChildren []         _        _   = nothing
    unifyAccChildren _          []       _   = nothing
    unifyAccChildren (t₁ ∷ ts₁) (t₂ ∷ ts₂) acc = unifyAcc t₁ t₂ acc >>= unifyAccChildren ts₁ ts₂

  unify : ∀ {m} → (t₁ t₂ : Term m) → Maybe (∃ (Subst m))
  unify {m} t₁ t₂ = unifyAcc t₁ t₂ (m , nil)

