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
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; cong)

module Unification (Symbol : Set) (arity : Symbol → ℕ) (decEqSym : Decidable {A = Symbol} _≡_) where

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
  Con : (s : Symbol) → (ts : Vec (Term n) (arity s)) → Term n

-- defining decidable equality on terms

{- strangely, using the following definition doesn't pass the termination checker
 - decEqVec : ∀ {ℓ} {n} {A : Set ℓ} (eq : Decidable {A = A} _≡_) → Decidable {A = Vec A n} _≡_
 - decEqVec eq [] [] = yes refl
 - decEqVec eq (x ∷ xs) ( y ∷  ys) with eq x y | decEqVec eq xs ys
 - decEqVec eq (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
 - decEqVec eq (x ∷ xs) (.x ∷  ys) | yes refl | no xs≢ys = no (xs≢ys ∘ cong tail)
 - decEqVec eq (x ∷ xs) ( y ∷  ys) | no x≢y   | _        = no (x≢y ∘ cong head)
 -}

mutual
  decEqTerm : ∀ {n} → Decidable {A = Term n} _≡_
  decEqTerm (Var x₁) (Var x₂) with x₁ ≟ x₂
  decEqTerm (Var .x₂) (Var x₂) | yes refl = yes refl
  decEqTerm (Var x₁) (Var x₂) | no x₁≢x₂ = no (x₁≢x₂ ∘ lem)
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

-- correctness of replacement function

mutual
  -- | proof that Var is the identity of replace
  replace-id : ∀ {n} (t : Term n) → replace Var t ≡ t
  replace-id (Var x)    = refl
  replace-id (Con s ts) = cong (Con s) (replaceChildren-id ts)

  -- | proof that Var is the identity of replaceChildren
  replaceChildren-id : ∀ {n k} (ts : Vec (Term n) k) → replaceChildren Var ts ≡ ts
  replaceChildren-id [] = refl
  replaceChildren-id (t ∷ ts) rewrite replace-id t = cong (_∷_ _) (replaceChildren-id ts)

-- defining substitution/replacement composition

_◇_ : ∀ {m n l} (f : Fin m → Term n) (g : Fin l → Term m) → Fin l → Term n
_◇_ f g = replace f ∘ g

-- correctness of substitution/replacement composition

mutual
  -- | proof that _◇_ behaves as composition of replacements
  ◇-replace
    : ∀ {m n l} (f : Fin m → Term n) (g : Fin l → Term m) (t : Term l)
    → replace (f ◇ g) t ≡ replace f (replace g t)
  ◇-replace f g (Var x) = refl
  ◇-replace f g (Con s ts) = cong (Con s) (◇-replaceChildren f g ts)

  -- | proof that _◇_ behaves as composition of replacements
  ◇-replaceChildren
    : ∀ {m n l k} (f : Fin m → Term n) (g : Fin l → Term m) (ts : Vec (Term l) k)
    → replaceChildren (f ◇ g) ts ≡ replaceChildren f (replaceChildren g ts)
  ◇-replaceChildren f g [] = refl
  ◇-replaceChildren f g (t ∷ ts) rewrite ◇-replace f g t = cong (_∷_ _) (◇-replaceChildren f g ts)

-- | proof that `Var ∘ _` is the identity of ◇
◇-identity
  : ∀ {m n l} (f : Fin m → Term n) (r : Fin l → Fin m) (t : Term l)
  → f ◇ (Var ∘ r) ≡ f ∘ r
◇-identity f r t = refl

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
thin-injective
  : ∀ {n} (x : Fin (suc n)) (y z : Fin n)
  → thin x y ≡ thin x z → y ≡ z
thin-injective {zero}   zero    ()      _       _
thin-injective {zero}  (suc _)  ()      _       _
thin-injective {suc _}  zero    zero    zero    refl = refl
thin-injective {suc _}  zero    zero   (suc _)  ()
thin-injective {suc _}  zero   (suc _)  zero    ()
thin-injective {suc _}  zero   (suc y) (suc .y) refl = refl
thin-injective {suc _} (suc _)  zero    zero    refl = refl
thin-injective {suc _} (suc _)  zero   (suc _)  ()
thin-injective {suc _} (suc _) (suc _)  zero    ()
thin-injective {suc n} (suc x) (suc y) (suc z)  p
  = cong suc (thin-injective x y z (cong pred p))

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

-- | proof that thick x composed with thin x is the identity
thickx∘thinx≡yes
  : ∀ {n} (x : Fin (suc n)) (y : Fin n)
  → thick x (thin x y) ≡ just y
thickx∘thinx≡yes  zero    zero   = refl
thickx∘thinx≡yes  zero   (suc _) = refl
thickx∘thinx≡yes (suc _)  zero   = refl
thickx∘thinx≡yes (suc x) (suc y) = cong (_<$>_ suc) (thickx∘thinx≡yes x y)

-- | proof that `thin` is a partial inverse of `thick`
thin≡thick⁻¹
  : ∀ {n} (x : Fin (suc n)) (y : Fin n) (z : Fin (suc n))
  → thin x y ≡ z
  → thick x z ≡ just y
thin≡thick⁻¹ x y z p with p
thin≡thick⁻¹ x y .(thin x y) _ | refl = thickx∘thinx≡yes x y

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
  check x₁ (Con s ts) = Con s <$> checkChildren x₁ ts


  checkChildren : ∀ {n k} (x : Fin (suc n)) (ts : Vec (Term (suc n)) k) → Maybe (Vec (Term n) k)
  checkChildren x₁ [] = just []
  checkChildren x₁ (t ∷ ts) = check x₁ t >>= λ t' →
                              checkChildren x₁ ts >>= λ ts' →
                              return (t' ∷ ts')

-- defining an occurs predicate that tests if x occurs in a term t

mutual
  data Occurs {n : ℕ} (x : Fin n) : Term n → Set where
    Here    : Occurs x (Var x)
    Further : ∀ {s ts} → OccursChildren x ts → Occurs x (Con s ts)

  data OccursChildren {n : ℕ} (x : Fin n) : {k : ℕ} → Vec (Term n) k → Set where
    Here    : ∀ {k t ts} → Occurs x t → OccursChildren x {suc k} (t ∷ ts)
    Further : ∀ {k t ts} → OccursChildren x {k} ts → OccursChildren x {suc k} (t ∷ ts)

-- defining a decidable version of the occurs predicate

mutual
  occurs? : ∀ {n} (x : Fin n) (t : Term n) → Dec (Occurs x t)
  occurs?  x₁ (Var x₂) with x₁ ≟ x₂
  occurs? .x₂ (Var x₂) | yes refl = yes Here
  occurs?  x₁ (Var x₂) | no x₁≢x₂ = no (x₁≢x₂ ∘ lem x₁ x₂)
    where
    lem : ∀ {n} (x y : Fin n) → Occurs x (Var y) → x ≡ y
    lem  zero    zero    _    = refl
    lem  zero   (suc _)  ()
    lem (suc x)  zero    ()
    lem (suc x) (suc .x) Here = refl
  occurs?  x₁ (Con s ts) with occursChildren? x₁ ts
  occurs?  x₁ (Con s ts) | yes x₁∈ts = yes (Further x₁∈ts)
  occurs?  x₁ (Con s ts) | no  x₁∉ts = no (x₁∉ts ∘ lem x₁)
    where
    lem : ∀ {n s ts} (x : Fin n) → Occurs x (Con s ts) → OccursChildren x ts
    lem x (Further p) = p

  occursChildren? : ∀ {n k} (x : Fin n) (ts : Vec (Term n) k) → Dec (OccursChildren x ts)
  occursChildren? x₁ [] = no (λ ())
  occursChildren? x₁ (t ∷ ts) with occurs? x₁ t
  occursChildren? x₁ (t ∷ ts) | yes h = yes (Here h)
  occursChildren? x₁ (t ∷ ts) | no ¬h with occursChildren? x₁ ts
  occursChildren? x₁ (t ∷ ts) | no ¬h | yes f = yes (Further f)
  occursChildren? x₁ (t ∷ ts) | no ¬h | no ¬f = no lem
    where
    lem : OccursChildren x₁ (t ∷ ts) → ⊥
    lem (Here p)    = ¬h p
    lem (Further p) = ¬f p

-- proving correctness of check

mutual
  -- | proving that if x occurs in t, check returns nothing
  occurs→check≡no
    : ∀ {n} (x : Fin (suc n)) (t : Term (suc n))
    → Occurs x t → check x t ≡ nothing
  occurs→check≡no x .(Var x) Here
    rewrite thickxx≡no x = refl
  occurs→check≡no x .(Con s ts) (Further {s} {ts} p)
    rewrite occursChildren→checkChildren≡no x ts p = refl

  -- | proving that if x occurs in ts, checkChildren returns nothing
  occursChildren→checkChildren≡no
    : ∀ {n k} (x : Fin (suc n)) (ts : Vec (Term (suc n)) k)
    → OccursChildren x ts → checkChildren x ts ≡ nothing
  occursChildren→checkChildren≡no x .(t ∷ ts) (Here {k} {t} {ts} p)
    rewrite occurs→check≡no x t p = refl
  occursChildren→checkChildren≡no x .(t ∷ ts) (Further {k} {t} {ts} p)
    with check x t
  ... | just  _ rewrite occursChildren→checkChildren≡no x ts p = refl
  ... | nothing rewrite occursChildren→checkChildren≡no x ts p = refl

mutual
  check≡no→occurs
    : ∀ {n} (x : Fin (suc n)) (t : Term (suc n))
    → check x t ≡ nothing → Occurs x t
  check≡no→occurs  x₁ (Var x₂) p with x₁ ≟ x₂
  check≡no→occurs .x₂ (Var x₂) p | yes refl = Here
  check≡no→occurs  x₁ (Var x₂) p | no x₁≢x₂ = ⊥-elim (lem₂ p)
    where
    lem₁ : ∃ (λ z → thick x₁ x₂ ≡ just z)
    lem₁ = x≢y→thickxy≡yes x₁ x₂ x₁≢x₂
    lem₂ : Var <$> thick x₁ x₂ ≡ nothing → ⊥
    lem₂ rewrite proj₂ lem₁ = λ ()
  check≡no→occurs x₁ (Con s ts) p = {!!}

  checkChildren≡no→occursChildren
    : ∀ {n k} (x : Fin (suc n)) (ts : Vec (Term (suc n)) k)
    → checkChildren x ts ≡ nothing → OccursChildren x ts
  checkChildren≡no→occursChildren x [] ()
  checkChildren≡no→occursChildren x (t ∷ ts) p with check x t | checkChildren x ts
  checkChildren≡no→occursChildren x (t ∷ ts) refl | nothing | _       = Here (check≡no→occurs x t {!!})
  checkChildren≡no→occursChildren x (t ∷ ts) refl | just  _ | nothing = Further (checkChildren≡no→occursChildren x ts {!!})
  checkChildren≡no→occursChildren x (t ∷ ts) ()   | just  _ | just  _


-- defining substitutions (AList in McBride, 2003)

data Subst : ℕ → ℕ → Set where
  nil  : ∀ {n}   → Subst n n
  snoc : ∀ {m n} → (s : Subst m n) → (t : Term m) → (x : Fin (suc m)) → Subst (suc m) n

-- defining function substituting t for x (**for** in McBride, 2003)

_for_ : ∀ {n} (t : Term n) (x : Fin (suc n)) → Fin (suc n) → Term n
_for_ t x y with thick x y
_for_ t x y | just y' = Var y'
_for_ t x y | nothing = t

-- proving correctness of _for_

for-identity
  : ∀ {n} (t : Term n) (x : Fin (suc n)) (y : Fin n)
  → (t for x) (thin x y) ≡ Var y
for-identity t x y rewrite thickx∘thinx≡yes x y = refl

-- defining substitution application (**sub** in McBride, 2003)

apply : ∀ {m n} → Subst m n → Fin m → Term n
apply nil = Var
apply (snoc s t x) = (apply s) ◇ (t for x)
