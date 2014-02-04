open import Function using (_∘_)
open import Category.Monad
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Props as FinProps using ()
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.List as List hiding (_++_)
open import Data.List.Properties using (∷-injective)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong)

module Unification (TermName : Set) (decEqTermName : (x y : TermName) → Dec (x ≡ y)) where

  private
    open RawMonad {{...}}
    open DecSetoid {{...}} using (_≟_)
    MaybeMonad         = Maybe.monad
    NatDecSetoid       = PropEq.decSetoid Nat._≟_
    FinDecSetoid       : ∀ {n} → DecSetoid _ _
    FinDecSetoid   {n} = FinProps.decSetoid n
    TermNameDecSetoid  : DecSetoid _ _
    TermNameDecSetoid  = PropEq.decSetoid decEqTermName

  -- defining terms
  data Term (n : ℕ) : Set where
    var : (x : Fin n) → Term n
    con : (s : TermName) (ts : List (Term n)) → Term n

  var-injective : ∀ {n x₁ x₂} → var {n} x₁ ≡ var {n} x₂ → x₁ ≡ x₂
  var-injective refl = refl

  con-injective : ∀ {n s₁ s₂ ts₁ ts₂} → con {n} s₁ ts₁ ≡ con {n} s₂ ts₂ → s₁ ≡ s₂ × ts₁ ≡ ts₂
  con-injective refl = (refl , refl)

  -- defining decidable equality on terms
  mutual
    decEqTerm : ∀ {n} → (t₁ t₂ : Term n) → Dec (t₁ ≡ t₂)
    decEqTerm (var  x₁) (var x₂) with x₁ ≟ x₂
    decEqTerm (var .x₂) (var x₂) | yes refl = yes refl
    decEqTerm (var  x₁) (var x₂) | no x₁≢x₂ = no (x₁≢x₂ ∘ var-injective)
    decEqTerm (var _)   (con _ _) = no (λ ())
    decEqTerm (con _ _) (var _)   = no (λ ())
    decEqTerm (con s₁ ts₁) (con  s₂  ts₂) with s₁ ≟ s₂
    decEqTerm (con s₁ ts₁) (con  s₂  ts₂) | no s₁≢s₂ = no (s₁≢s₂ ∘ proj₁ ∘ con-injective)
    decEqTerm (con s₁ ts₁) (con .s₁  ts₂) | yes refl with decEqTermList ts₁ ts₂
    decEqTerm (con s₁ ts₁) (con .s₁  ts₂) | yes refl | no ts₁≢ts₂ = no (ts₁≢ts₂ ∘ proj₂ ∘ con-injective)
    decEqTerm (con s₁ ts₁) (con .s₁ .ts₁) | yes refl | yes refl = yes refl

    decEqTermList : ∀ {n} (xs ys : List (Term n)) → Dec (xs ≡ ys)
    decEqTermList [] [] = yes refl
    decEqTermList [] (_  ∷ _) = no (λ ())
    decEqTermList (_ ∷ _) [] = no (λ ())
    decEqTermList (x ∷ xs) ( y ∷  ys) with decEqTerm x y
    decEqTermList (x ∷ xs) ( y ∷  ys) | no x≢y = no (x≢y ∘ proj₁ ∘ ∷-injective)
    decEqTermList (x ∷ xs) (.x ∷  ys) | yes refl with decEqTermList xs ys
    decEqTermList (x ∷ xs) (.x ∷  ys) | yes refl | no xs≢ys = no (xs≢ys ∘ proj₂ ∘ ∷-injective)
    decEqTermList (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl


  private
    TermDecSetoid : ∀ {n} → DecSetoid _ _
    TermDecSetoid {n} = PropEq.decSetoid (decEqTerm {n})


  -- defining replacement function (written _◂ in McBride, 2003)
  mutual
    replace : ∀ {n m} → (Fin n → Term m) → Term n → Term m
    replace f (var i)  = f i
    replace f (con s ts) = con s (replaceChildren f ts)

    replaceChildren : ∀ {n m} → (Fin n → Term m) → (List (Term n) → List (Term m))
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


  -- defining an occurs check (**check** in McBride, 2003)
  mutual
    check : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) → Maybe (Term n)
    check x₁ (var x₂)   = var <$> thick x₁ x₂
    check x₁ (con s ts) = con s <$> checkChildren x₁ ts

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

  mutual
    unifyAcc : ∀ {m} → (t₁ t₂ : Term m) → ∃ (Subst m) → Maybe (∃ (Subst m))
    unifyAcc (con s₁ ts₁) (con  s₂ ts₂) acc with s₁ ≟ s₂
    unifyAcc (con s₁ ts₁) (con .s₁ ts₂) acc | yes refl = unifyAccChildren ts₁ ts₂ acc
    unifyAcc (con s₁ ts₁) (con  s₂ ts₂) acc | no s₁≢s₂ = nothing
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
