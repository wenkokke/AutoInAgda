open import Auto
open import Function using (id; const)
open import Data.Bin as Bin using (Bin) renaming (0# to bin; toℕ to bin2nat)
open import Data.List as List using (List; _∷_; [])
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Show using () renaming (show to nat2str)
open import Data.String using (String)
open import Reflection

module Auto.Example where

  data Even  : ℕ →  Set where
    isEven0  : Even 0
    isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

  hints : HintDB
  hints = hintdb (quote isEven0 ∷ quote isEven+2 ∷ [])

  test₁ : Even 4
  test₁ = quoteGoal g in unquote (auto 5 hints g)

  test₂ : ∀ {n} → Even n → Even (suc (suc (suc (suc n))))
  test₂ = quoteGoal g in unquote (auto 5 hints g)
