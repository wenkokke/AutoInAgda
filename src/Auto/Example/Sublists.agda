open import Function      using (flip; _∘_; _$_)
open import Auto.Core     using (dfs)
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

db₁ : HintDB
db₁ = ε <<[ 2 ] quote trans
        
test₁ : {A : Set} {ws xs ys zs : List A} → ws ⊆ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆ zs
test₁ = tactic (auto dfs 10 db₁)

db₂ : HintDB
db₂ = ε <<[ 1 ] quote trans

test₂ : Exception searchSpaceExhausted
test₂ = unquote (auto dfs 10 db₂ (quoteTerm
                ({A : Set} {ws xs ys zs : List A} → ws ⊆ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆ zs)))

db₃ : HintDB
db₃ = ε <<[ 1 ] quote trans
        <<      quote drop
        <<      quote keep

test₃ : {xs ys zs : List ℕ} → xs ⊆ ys → ys ⊆ zs → xs ⊆ 1 ∷ 2 ∷ zs
test₃ = tactic (auto dfs 5 db₃)
