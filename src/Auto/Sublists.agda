module Auto.Sublists where

open import Auto
open import Data.List using (List; _∷_; [])

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
