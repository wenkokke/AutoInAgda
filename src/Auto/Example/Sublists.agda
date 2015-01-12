open import Function      using (flip; _∘_; _$_)
open import Auto.Counting
open import Data.Nat      using (ℕ)
open import Data.List     using (List; _∷_; [])
open import Data.Product  using (∃; _,_; proj₂)
open import Data.Maybe    
open import Data.Sum      using (inj₁; inj₂; isInj₂)

module Auto.Example.Sublists where


infix 3 _⊆_

data _⊆_ {a} {A : Set a} : List A → List A → Set a where
  stop : [] ⊆ []
  drop : ∀ {xs y ys} → xs ⊆ ys →     xs ⊆ y ∷ ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys


refl : ∀ {a} {A : Set a} {xs : List A} → xs ⊆ xs
refl {xs = []}     = stop
refl {xs = x ∷ xs} = keep refl

trans : ∀ {a} {A : Set a} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
trans       p   stop    = p
trans       p  (drop q) = drop (trans p q)
trans (drop p) (keep q) = drop (trans p q)
trans (keep p) (keep q) = keep (trans p q)

hintdb₁ : HintDB
hintdb₁ = ε << quote drop
            << quote keep
            << quote trans

lemma₁ : {ws xs ys zs : List ℕ}
       → ws ⊆ 1 ∷ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆ 1 ∷ 2 ∷ zs
lemma₁ = tactic (auto dfs 10 hintdb₁)

lemma₂ : {ws xs ys zs : List ℕ}
       → ws ⊆ 1 ∷ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆     2 ∷ zs
lemma₂ = tactic (auto dfs 10 hintdb₁)


{-
db₂ : HintDB
db₂ = ε << quote trans
        << quote keep
        << quote drop

test₂ : {A : Set} {ws xs ys zs : List A} → ws ⊆ xs → ys ⊆ zs → ws ⊆ zs
test₂ = tactic (auto dfs 10 db₁)
-}
