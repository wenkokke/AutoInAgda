open import Function using (_∘_)
open import Category.Functor
open import Data.Fin using (Fin; zero; suc; raise)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; cong)

module Unification (Op : Set) (arity : Op → ℕ) (decEqOp : Decidable {A = Op} _≡_) where

data Term (n : ℕ) : Set where
  Var : Fin n → Term n
  Con : (x : Op) → (xs : Vec (Term n) (arity x)) → Term n

open RawFunctor {{...}}

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
  where
  functor = Maybe.functor

-- correctness of thin

inject-thin : ∀ {n} → (x : Fin (suc n)) (y z : Fin n) → thin x y ≡ thin x z → y ≡ z
inject-thin {zero}   zero    ()      _       _
inject-thin {zero}  (suc _)  ()      _       _
inject-thin {suc _}  zero    zero    zero    refl = refl
inject-thin {suc _}  zero    zero   (suc _)  ()
inject-thin {suc _}  zero   (suc _)  zero    ()
inject-thin {suc _}  zero   (suc y) (suc .y) refl = refl
inject-thin {suc _} (suc _)  zero    zero    refl = refl
inject-thin {suc _} (suc _)  zero   (suc _)  ()
inject-thin {suc _} (suc _) (suc _)  zero    ()
inject-thin {suc n} (suc x) (suc y) (suc z)  p
  = cong suc (inject-thin {n} x y z (cong pred p))
  where
  pred : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
  pred  zero   = zero
  pred (suc x) = x

thinxy≢x : ∀ {n} → (x : Fin (suc n)) (y z : Fin n) → thin x y ≢ x
thinxy≢x  zero    _       _      = λ ()
thinxy≢x (suc _)  zero    _      = λ ()
thinxy≢x (suc x) (suc y)  zero   = {!!}
thinxy≢x (suc x) (suc y) (suc z) = {!!}

-- defining substitutions (AList in McBride, 2003)

data Subst : ℕ → ℕ → Set where
  Nil  : ∀ {n} → Subst n n
  Snoc : ∀ {m n} → Subst m n → Term m → Fin (suc m) → Subst (suc m) n

-- defining substitution (**sub** in McBride, 2003)

-- apply : {n m : ℕ} → Subst n m → Fin n → Term m
-- apply Nil = Var
-- apply (Snoc σ t x) = apply subst ⋄ (t for i)

mutual
  replace : {n m : ℕ} → (Fin n → Term m) → Term n → Term m
  replace f (Var i) = f i
  replace f (Con x xs) = Con x (replaceChildren f xs)

  replaceChildren : {n m k : ℕ} → (Fin n → Term m) → Vec (Term n) k → Vec (Term m) k
  replaceChildren f [] = []
  replaceChildren f (x ∷ xs) = replace f x ∷ (replaceChildren f xs)
