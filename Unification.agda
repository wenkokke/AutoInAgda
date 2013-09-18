open import Function using (_∘_)
open import Category.Functor
open import Category.Monad
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Props as FinProps using ()
open import Data.Maybe as Maybe using (Maybe; maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Equality as VecEq
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary as Bin using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; cong)

module Unification (Op : Set) (arity : Op → ℕ) (decEqOp : Decidable {A = Op} _≡_) where

open RawFunctor {{...}}
open RawMonad {{...}} hiding (_<$>_)
open Bin.DecSetoid {{...}} using (_≟_)

finDecSetoid : ∀ {n} → DecSetoid _ _
finDecSetoid {n} = FinProps.decSetoid n
maybeFunctor = Maybe.functor
maybeMonad = Maybe.monad

-- defining terms

data Term (n : ℕ) : Set where
  Var : Fin n → Term n
  Con : (x : Op) → (xs : Vec (Term n) (arity x)) → Term n

-- defining replacement function (written _◂ in McBride, 2003)

mutual
  replace : ∀ {n m} → (Fin n → Term m) → Term n → Term m
  replace f (Var i)    = f i
  replace f (Con x xs) = Con x (replaceChildren f xs)

  replaceChildren : ∀ {n m k} → (Fin n → Term m) → Vec (Term n) k → Vec (Term m) k
  replaceChildren f []       = []
  replaceChildren f (x ∷ xs) = replace f x ∷ (replaceChildren f xs)

-- correctness of replacement function

mutual
  -- | proof that Var is the identity of replace
  replace-id : ∀ {n} (t : Term n) → replace Var t ≡ t
  replace-id (Var x)    = refl
  replace-id (Con x xs) = cong (Con x) (replaceChildren-id xs)

  -- | proof that Var is the identity of replaceChildren
  replaceChildren-id : ∀ {n k} (ts : Vec (Term n) k) → replaceChildren Var ts ≡ ts
  replaceChildren-id [] = refl
  replaceChildren-id (t ∷ ts) rewrite replace-id t = cong (_∷_ _) (replaceChildren-id ts)

-- defining substitution/replacement composition

_◇_ : ∀ {m n l} (f : Fin m → Term n) (g : Fin l → Term m) → Fin l → Term n
_◇_ f g = replace f ∘ g

-- correctness of substitution/replacement composition

mutual
  -- | proof that ◇ rewrites to applications of replace
  replace-◇
    : ∀ {m n l} (f : Fin m → Term n) (g : Fin l → Term m) (t : Term l)
    → replace (f ◇ g) t ≡ replace f (replace g t)
  replace-◇ f g (Var x) = refl
  replace-◇ f g (Con x xs) = cong (Con x) (replaceChildren-◇ f g xs)

  -- | proof that ◇ rewrites to applications of replace
  replaceChildren-◇
    : ∀ {m n l k} (f : Fin m → Term n) (g : Fin l → Term m) (ts : Vec (Term l) k)
    → replaceChildren (f ◇ g) ts ≡ replaceChildren f (replaceChildren g ts)
  replaceChildren-◇ f g [] = refl
  replaceChildren-◇ f g (t ∷ ts) rewrite replace-◇ f g t = cong (_∷_ _) (replaceChildren-◇ f g ts)

-- | proof that `Var ∘ _` is the identity of ◇
◇-id
  : ∀ {m n l} (f : Fin m → Term n) (r : Fin l → Fin m) (t : Term l)
  → f ◇ (Var ∘ r) ≡ f ∘ r
◇-id f r t = refl



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

-- proving correctness of thick and thin

-- | predecessor function over finite numbers
pred : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
pred  zero   = zero
pred (suc x) = x

-- | proof of injectivity of thin
thinxy≡thinxz→y≡z
  : ∀ {n} (x : Fin (suc n)) (y z : Fin n)
  → thin x y ≡ thin x z → y ≡ z
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
  = cong suc (thinxy≡thinxz→y≡z x y z (cong pred p))

-- | proof that thin x will never map anything to x
thinxy≢x
  : ∀ {n} (x : Fin (suc n)) (y : Fin n)
  → thin x y ≢ x
thinxy≢x  zero    zero   ()
thinxy≢x  zero   (suc _) ()
thinxy≢x (suc _)  zero   ()
thinxy≢x (suc x) (suc y) p
  = thinxy≢x x y (cong pred p)

-- | proof that `thin x` reaches all y where x ≢ y
x≢y→thinxz≡y
  : ∀ {n} (x y : Fin (suc n))
  → x ≢ y → ∃ (λ z → thin x z ≡ y)
x≢y→thinxz≡y          zero     zero 0≢0 with 0≢0 refl
x≢y→thinxz≡y          zero     zero 0≢0 | ()
x≢y→thinxz≡y {zero}  (suc ())  _       _
x≢y→thinxz≡y {zero}   zero    (suc ()) _
x≢y→thinxz≡y {suc _}  zero    (suc y)  _ = y , refl
x≢y→thinxz≡y {suc _} (suc x)   zero    _ = zero , refl
x≢y→thinxz≡y {suc _} (suc x)  (suc y)  sx≢sy
  = (suc (proj₁ prf)) , (lem x y (proj₁ prf) (proj₂ prf))
  where
  x≢y = sx≢sy ∘ cong suc
  prf = x≢y→thinxz≡y x y x≢y
  lem : ∀ {n} (x y : Fin (suc n)) (z : Fin n)
      → thin x z ≡ y → thin (suc x) (suc z) ≡ suc y
  lem  zero    zero              _      ()
  lem  zero    (suc .z)          z      refl = refl
  lem (suc _)  zero              zero   refl = refl
  lem (suc _)  zero             (suc _) ()
  lem (suc _) (suc _)            zero   ()
  lem (suc x) (suc .(thin x z)) (suc z) refl = refl

-- | proof that `thin` is a partial inverse of `thick`
thin≡thick⁻¹
  : ∀ {n} (x : Fin (suc n)) (y : Fin n) (z : Fin (suc n))
  → thin x y ≡ z
  → thick x z ≡ just y
thin≡thick⁻¹ x y z p with p
thin≡thick⁻¹ x y .(thin x y) _ | refl = thickthin x y
  where
  thickthin
    : ∀ {n} (x : Fin (suc n)) (y : Fin n)
    → thick x (thin x y) ≡ just y
  thickthin  zero    zero   = refl
  thickthin  zero   (suc _) = refl
  thickthin (suc _)  zero   = refl
  thickthin (suc x) (suc y) = cong (_<$>_ suc) (thickthin x y)

-- | decidable equality for Fin (import from FinProps)
-- decEqFin : ∀ {n} → Decidable {A = Fin n} _≡_
-- decEqFin {n} = DecSetoid._≟_ (FinProps.decSetoid n)

-- | proof that `thick x x` returns nothing
thickxx≡no
  : ∀ {n} (x : Fin (suc n))
  → thick x x ≡ nothing
thickxx≡no zero = refl
thickxx≡no {zero}  (suc ())
thickxx≡no {suc n} (suc x)
  = cong (maybe (λ x → just (suc x)) nothing) (thickxx≡no x)

-- | proof that `thick x y` returns something when x ≢ y
x≢y→thickxy≡yes
  : ∀ {n} (x y : Fin (suc n))
  → x ≢ y → ∃ (λ z → thick x y ≡ just z)
x≢y→thickxy≡yes zero zero 0≢0 with 0≢0 refl
x≢y→thickxy≡yes zero zero 0≢0 | ()
x≢y→thickxy≡yes zero (suc y) p = y , refl
x≢y→thickxy≡yes {zero}  (suc ())  _ _
x≢y→thickxy≡yes {suc n} (suc x) zero _ = zero , refl
x≢y→thickxy≡yes {suc n} (suc x) (suc y) sx≢sy
  = (suc (proj₁ prf)) , (cong (_<$>_ suc) (proj₂ prf))
  where
  x≢y = sx≢sy ∘ cong suc
  prf = x≢y→thickxy≡yes {n} x y x≢y

-- | proof that `thick` is the partial inverse of `thin`
thick≡thin⁻¹ : ∀ {n} (x y : Fin (suc n)) (r : Maybe (Fin n))
  → thick x y ≡ r
  → x ≡ y ∧ r ≡ nothing
  ⊎ ∃ (λ z → thin x z ≡ y ∧ r ≡ just z)
thick≡thin⁻¹ x  y _ thickxy≡r with x ≟ y | thickxy≡r
thick≡thin⁻¹ x .x .(thick x x) _ | yes refl | refl
  = inj₁ (refl , thickxx≡no x)
thick≡thin⁻¹ x  y .(thick x y) _ | no  x≢y  | refl
  = inj₂ (proj₁ prf₁ , (proj₂ prf₁) , prf₂)
  where
  prf₁ = x≢y→thinxz≡y x y x≢y
  prf₂ = thin≡thick⁻¹ x (proj₁ prf₁) y (proj₂ prf₁)

-- defining an occurs check (**check** in McBride, 2003)

mutual
  check : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) → Maybe (Term n)
  check x₁ (Var x₂) = Var <$> thick x₁ x₂
  check x₁ (Con op xs) = Con op <$> checkChildren x₁ xs


  checkChildren : ∀ {n k} (x : Fin (suc n)) (ts : Vec (Term (suc n)) k) → Maybe (Vec (Term n) k)
  checkChildren x₁ [] = just []
  checkChildren x₁ (t ∷ ts) = check x₁ t >>= λ t' →
                              checkChildren x₁ ts >>= λ ts' →
                              return (t' ∷ ts')

checkCorrect
  : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) (t' : Term n)
  → check x t ≡ just t' → replace (Var ∘ thin x) t' ≡ t
checkCorrect x t t' p = {!!}

-- defining substitutions (AList in McBride, 2003)

data Subst : ℕ → ℕ → Set where
  Nil  : ∀ {n} → Subst n n
  Snoc : ∀ {m n} → Subst m n → Term m → Fin (suc m) → Subst (suc m) n

-- defining substitution (**sub** in McBride, 2003)

-- apply : {n m : ℕ} → Subst n m → Fin n → Term m
-- apply Nil = Var
-- apply (Snoc σ t x) = apply subst ⋄ (t for i)
