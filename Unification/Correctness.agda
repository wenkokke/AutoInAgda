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
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; cong; inspect; Reveal_is_; [_])

module Unification.Correctness (Symbol : Set) (arity : Symbol → ℕ) (decEqSym : (s₁ s₂ : Symbol) → Dec (s₁ ≡ s₂)) where

  import Unification
  module UI = Unification Symbol arity decEqSym
  open UI

  open RawFunctor {{...}}
  open DecSetoid {{...}} using (_≟_)

  private maybeFunctor = Maybe.functor
  private finDecSetoid : ∀ {n} → DecSetoid _ _
          finDecSetoid {n} = FinProps.decSetoid n

  -- * proving correctness of replacement function

  mutual
    -- | proof that var is the identity of replace
    replace-thm₁ : ∀ {n} (t : Term n) → replace var t ≡ t
    replace-thm₁ (var x)    = refl
    replace-thm₁ (con s ts) = cong (con s) (replaceChildren-thm₁ ts)

    -- | proof that var is the identity of replaceChildren
    replaceChildren-thm₁ : ∀ {n k} (ts : Vec (Term n) k) → replaceChildren var ts ≡ ts
    replaceChildren-thm₁ [] = refl
    replaceChildren-thm₁ (t ∷ ts) rewrite replace-thm₁ t = cong (_∷_ _) (replaceChildren-thm₁ ts)



  -- * proving correctness of substitution/replacement composition

  -- | proof that `var ∘ _` is the identity of ◇
  compose-thm₁
    : ∀ {m n l} (f : Fin m → Term n) (r : Fin l → Fin m) (t : Term l)
    → f ◇ (var ∘ r) ≡ f ∘ r
  compose-thm₁ f r t = refl

  mutual
    -- | proof that _◇_ behaves as composition of replacements
    compose-thm₂
      : ∀ {m n l} (f : Fin m → Term n) (g : Fin l → Term m) (t : Term l)
      → replace (f ◇ g) t ≡ replace f (replace g t)
    compose-thm₂ f g (var x) = refl
    compose-thm₂ f g (con s ts) = cong (con s) (composeChildren-thm₂ f g ts)

    -- | proof that _◇_ behaves as composition of replacements
    composeChildren-thm₂
      : ∀ {m n l k} (f : Fin m → Term n) (g : Fin l → Term m) (ts : Vec (Term l) k)
      → replaceChildren (f ◇ g) ts ≡ replaceChildren f (replaceChildren g ts)
    composeChildren-thm₂ f g [] = refl
    composeChildren-thm₂ f g (t ∷ ts) rewrite compose-thm₂ f g t = cong (_∷_ _) (composeChildren-thm₂ f g ts)



  -- * proving correctness of thick and thin

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

  -- | proof that if check returns nothing, checkChildren will too
  check≡no→checkChildren≡no
    : ∀ {n} (x : Fin (suc n)) (s : Symbol) (ts : Vec (Term (suc n)) (arity s))
    → check x (con s ts) ≡ nothing → checkChildren x ts ≡ nothing
  check≡no→checkChildren≡no x s ts p with checkChildren x ts
  check≡no→checkChildren≡no x s ts p  | nothing = refl
  check≡no→checkChildren≡no x s ts () | just _

  -- | proof that if check returns something, checkChildren will too
  check≡yes→checkChildren≡yes
    : ∀ {n} (x : Fin (suc n)) (s : Symbol) (ts : Vec (Term (suc n)) (arity s)) (ts' : Vec (Term n) (arity s))
    → check x (con s ts) ≡ just (con s ts') → checkChildren x ts ≡ just ts'
  check≡yes→checkChildren≡yes x s ts ts' p with checkChildren x ts
  check≡yes→checkChildren≡yes x s ts ts' refl | just .ts' = refl
  check≡yes→checkChildren≡yes x s ts ts' ()   | nothing

  -- | occurs predicate that is only inhabited if x occurs in t
  mutual
    data Occurs {n : ℕ} (x : Fin n) : Term n → Set where
      Here    : Occurs x (var x)
      Further : ∀ {s ts} → OccursChildren x ts → Occurs x (con s ts)

    data OccursChildren {n : ℕ} (x : Fin n) : {k : ℕ} → Vec (Term n) k → Set where
      Here    : ∀ {k t ts} → Occurs x t → OccursChildren x {suc k} (t ∷ ts)
      Further : ∀ {k t ts} → OccursChildren x {k} ts → OccursChildren x {suc k} (t ∷ ts)

  -- | proof of decidability for the occurs predicate
  mutual
    occurs? : ∀ {n} (x : Fin n) (t : Term n) → Dec (Occurs x t)
    occurs?  x₁ (var x₂) with x₁ ≟ x₂
    occurs? .x₂ (var x₂) | yes refl = yes Here
    occurs?  x₁ (var x₂) | no x₁≢x₂ = no (x₁≢x₂ ∘ lem x₁ x₂)
      where
      lem : ∀ {n} (x y : Fin n) → Occurs x (var y) → x ≡ y
      lem  zero    zero    _    = refl
      lem  zero   (suc _)  ()
      lem (suc x)  zero    ()
      lem (suc x) (suc .x) Here = refl
    occurs?  x₁ (con s ts) with occursChildren? x₁ ts
    occurs?  x₁ (con s ts) | yes x₁∈ts = yes (Further x₁∈ts)
    occurs?  x₁ (con s ts) | no  x₁∉ts = no (x₁∉ts ∘ lem x₁)
      where
      lem : ∀ {n s ts} (x : Fin n) → Occurs x (con s ts) → OccursChildren x ts
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

  -- * proving correctness of check

  mutual
    -- | proving that if x occurs in t, check returns nothing
    occurs→check≡no
      : ∀ {n} (x : Fin (suc n)) (t : Term (suc n))
      → Occurs x t → check x t ≡ nothing
    occurs→check≡no x .(var x) Here
      rewrite thickxx≡no x = refl
    occurs→check≡no x .(con s ts) (Further {s} {ts} p)
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
    -- | proof that if check x t returns nothing, x occurs in t
    check≡no→occurs
      : ∀ {n} (x : Fin (suc n)) (t : Term (suc n))
      → check x t ≡ nothing → Occurs x t
    check≡no→occurs  x₁ (var x₂) p with x₁ ≟ x₂
    check≡no→occurs .x₂ (var x₂) p | yes refl = Here
    check≡no→occurs  x₁ (var x₂) p | no x₁≢x₂ = ⊥-elim (lem₂ p)
      where
      lem₁ : ∃ (λ z → thick x₁ x₂ ≡ just z)
      lem₁ = x≢y→thickxy≡yes x₁ x₂ x₁≢x₂
      lem₂ : var <$> thick x₁ x₂ ≡ nothing → ⊥
      lem₂ rewrite proj₂ lem₁ = λ ()
    check≡no→occurs {n} x₁ (con s ts) p
      = Further (checkChildren≡no→occursChildren x₁ ts (lem p))
      where
      lem : con s <$> checkChildren x₁ ts ≡ nothing → checkChildren x₁ ts ≡ nothing
      lem p with checkChildren x₁ ts | inspect (checkChildren x₁) ts
      lem () | just  _ | [ eq ]
      lem p  | nothing | [ eq ] = refl

    -- | proof that if checkChildren x ts returns nothing, x occurs in ts
    checkChildren≡no→occursChildren
      : ∀ {n k} (x : Fin (suc n)) (ts : Vec (Term (suc n)) k)
      → checkChildren x ts ≡ nothing → OccursChildren x ts
    checkChildren≡no→occursChildren x [] ()
    checkChildren≡no→occursChildren x (t ∷ ts) p with check x t | inspect (check x) t
    ... | nothing | [ e₁ ] = Here (check≡no→occurs x t e₁)
    ... | just  _ | [ e₁ ] with checkChildren x ts | inspect (checkChildren x) ts
    ... | nothing | [ e₂ ] = Further (checkChildren≡no→occursChildren x ts e₂)
    checkChildren≡no→occursChildren x (t ∷ ts) () | just _ | [ e₁ ] | just _ | [ e₂ ]


  -- | proof that if check returns just, x does not occur in t
  check≡yes→¬occurs
    : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) (t' : Term n)
    → check x t ≡ just t' → ¬ (Occurs x t)
  check≡yes→¬occurs x t t' p₁ x∈t with occurs→check≡no x t x∈t
  check≡yes→¬occurs x t t' p₁ _   | p₂  with check x t
  check≡yes→¬occurs x t t' p₁ _   | ()  | just _
  check≡yes→¬occurs x t t' () _   | p₂  | nothing

  -- | proof that x does not occur in t, check returns just
  ¬occurs→check≡yes
    : ∀ {n} (x : Fin (suc n)) (t : Term (suc n))
    → ¬ (Occurs x t) → ∃ (λ t' → check x t ≡ just t')
  ¬occurs→check≡yes x t x∉t with check x t | inspect (check x) t
  ¬occurs→check≡yes x t x∉t | nothing | [ eq ] with x∉t (check≡no→occurs x t eq)
  ¬occurs→check≡yes x t x∉t | nothing | [ eq ] | ()
  ¬occurs→check≡yes x t x∉t | just t' | [ eq ] = t' , refl



  -- * proving correctness of _for_

  -- | proof that if there is nothing to unify, _for_ is the identity
  for-thm₁
    : ∀ {n} (t : Term n) (x : Fin (suc n)) (y : Fin n)
    → (t for x) (thin x y) ≡ var y
  for-thm₁ t x y rewrite thickx∘thinx≡yes x y = refl

  mutual
    -- | proof that if there is something to unify, _for_ unifies
    for-thm₂
      : ∀ {n} (x : Fin (suc n)) (t : Term (suc n)) (t' : Term n)
      → check x t ≡ just t' → replace (t' for x) t ≡ (t' for x) x
    for-thm₂  x (var y) _ _ with x ≟ y
    for-thm₂ .y (var y) _ _ | yes refl = refl
    for-thm₂  x (var y) _ _ | no x≢y
      with thick x y | x≢y→thickxy≡yes x y x≢y
         | thick x x | thickxx≡no x
    for-thm₂  x (var y) .(var z) refl | no _
         | .(just z) | z , refl
         | .nothing  | refl = refl
    for-thm₂  x (con s ts) _ _ with checkChildren x ts | inspect (checkChildren x) ts
    for-thm₂  x (con s ts) _ ()              | nothing  | _
    for-thm₂  x (con s ts) .(con s ts') refl | just ts' | [ checkChildren≡yes ] = {!!}

    forChildren-thm₂ : {!!}
    forChildren-thm₂ = {!!}

  -- * proving correctness of apply, concat and compose

  ++-thm₁ : ∀ {m n} (s : Subst m n) → nil ++ s ≡ s
  ++-thm₁ nil = refl
  ++-thm₁ (snoc s t x) = cong (λ s → snoc s t x) (++-thm₁ s)

  ++-lem₂
    : ∀ {l m n} (s₁ : Subst m n) (s₂ : Subst l m) (t : Term l)
    → replace (apply (s₁ ++ s₂)) t ≡ replace (apply s₁) (replace (apply s₂) t)
  ++-lem₂ s₁ nil t rewrite replace-thm₁ t = refl
  ++-lem₂ s₁ (snoc s₂ t₂ x) t = {!!}
    where
    lem : {!replace (apply (s₁ ++ s₂)) t ≡ !}
    lem = ++-lem₂ s₁ s₂ (replace (t₂ for x) t)

  ++-thm₂
    : ∀ {l m n} (s₁ : Subst m n) (s₂ : Subst l m) (x : Fin l)
    → apply (s₁ ++ s₂) x ≡ (apply s₁ ◇ apply s₂) x
  ++-thm₂ s₁ nil x = refl
  ++-thm₂ s₁ (snoc s₂ t y) x with thick y x
  ++-thm₂ s₁ (snoc s₂ t y) x | just t' = ++-thm₂ s₁ s₂ t'
  ++-thm₂ s₁ (snoc s₂ t y) x | nothing = lem
    where
    lem : replace (apply (s₁ ++ s₂)) t ≡ replace (apply s₁) (replace (apply s₂) t)
    lem = {!!}

{-
  ++-thm₂ .n       .n       n nil                 nil                 x = refl
  ++-thm₂ .(suc m) .(suc m) n (snoc {m} s₁ t₁ y₁) nil                 x = refl
  ++-thm₂ .(suc m) .n       n nil                 (snoc {m} s₂ t₂ y₂) x with thick y₂ x
  ++-thm₂ .(suc m) .n n nil (snoc {m} s₂ t₂ y₂) x | just t'
    rewrite ++-thm₁ s₂ | replace-thm₁ (apply s₂ t') = refl
  ++-thm₂ .(suc m) .n n nil (snoc {m} s₂ t₂ y₂) x | nothing
    rewrite ++-thm₁ s₂ | replace-thm₁ (replace (apply s₂) t₂) = refl
  ++-thm₂ .(suc l) .(suc m) n (snoc {m} s₁ t₁ y₁) (snoc {l} s₂ t₂ y₂) x = {!!}
-}
