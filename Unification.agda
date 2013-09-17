open import Function using (_∘_)
open import Category.Functor
open import Data.Fin using (Fin; zero; suc; raise)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂)
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

pred : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
pred  zero   = zero
pred (suc x) = x

thinxy≡thinxz→y≡z : ∀ {n} → (x : Fin (suc n)) (y z : Fin n) → thin x y ≡ thin x z → y ≡ z
thinxy≡thinxz→y≡z {zero}   zero    ()      _       _
thinxy≡thinxz→y≡z {zero}  (suc _)  ()      _       _
thinxy≡thinxz→y≡z {suc _}  zero    zero    zero    refl = refl
thinxy≡thinxz→y≡z {suc _}  zero    zero   (suc _)  ()
thinxy≡thinxz→y≡z {suc _}  zero   (suc _)  zero    ()
thinxy≡thinxz→y≡z {suc _}  zero   (suc y) (suc .y) refl = refl
thinxy≡thinxz→y≡z {suc _} (suc _)  zero    zero    refl = refl
thinxy≡thinxz→y≡z {suc _} (suc _)  zero   (suc _)  ()
thinxy≡thinxz→y≡z {suc _} (suc _) (suc _)  zero    ()
thinxy≡thinxz→y≡z {suc n} (suc x) (suc y) (suc z)  p
  = cong suc (thinxy≡thinxz→y≡z {n} x y z (cong pred p))

thinxy≢x : ∀ {n} → (x : Fin (suc n)) (y : Fin n) → thin x y ≢ x
thinxy≢x  zero    zero   ()
thinxy≢x  zero   (suc y) ()
thinxy≢x (suc x)  zero   ()
thinxy≢x (suc x) (suc y) p
  = thinxy≢x x y (cong pred p)

x≢y→thinxz≡y : ∀ {n} → (x y : Fin (suc (suc n))) → x ≢ y → ∃ (λ z → thin x z ≡ y)
x≢y→thinxz≡y  zero    zero   0≢0 with 0≢0 refl
x≢y→thinxz≡y  zero    zero   0≢0 | ()
x≢y→thinxz≡y  zero   (suc y) _ = y , refl
x≢y→thinxz≡y (suc x)  zero   _ = zero , refl
x≢y→thinxz≡y {zero} (suc (suc ())) _ _
x≢y→thinxz≡y {zero} (suc zero) (suc (suc ())) _
x≢y→thinxz≡y {zero} (suc zero) (suc zero) 1≢1 with 1≢1 refl
x≢y→thinxz≡y {zero} (suc zero) (suc zero) 1≢1 | ()
x≢y→thinxz≡y {suc n} (suc x) (suc y) sx≢sy
  = suc (proj₁ prf) , lem x y (proj₁ prf) (proj₂ prf)
  where
  x≢y = sx≢sy ∘ cong suc
  prf = x≢y→thinxz≡y x y x≢y
  lem : ∀ {n}
      → (x y : Fin (suc n)) (z : Fin n)
      → thin x z ≡ y → thin (suc x) (suc z) ≡ suc y
  lem zero zero _ ()
  lem zero (suc .z) z refl = refl
  lem (suc _) zero zero refl = refl
  lem (suc _) zero (suc _) ()
  lem (suc _) (suc _) zero ()
  lem (suc x) (suc .(thin x z)) (suc z) refl = refl

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
