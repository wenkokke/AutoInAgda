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

  evenSum : ∀ {n m} -> Even n -> Even m -> Even (n + m)
  evenSum isEven0 e2 = e2
  evenSum (isEven+2 e1) e2 = 
    let hints = hintdb (quote isEven+2 ∷ quote evenSum ∷ []) in
    quoteGoal g in {!unquote (auto 5 hints g)!}  --isEven+2 (evenSum e1 e2)

  simple : ∀ {n} → Even n → Even (n + 2)
  simple e =  evenSum e (isEven+2 isEven0)

  hints : HintDB
  hints = hintdb (quote isEven0 ∷ quote isEven+2 ∷ quote evenSum ∷ [])

  test₁ : Even 4
  test₁ = quoteGoal g in unquote (auto 5 hints g)

  test₂ : ∀ {n} → Even n → Even (suc (suc (suc (suc n))))
  test₂ = quoteGoal g in unquote (auto 5 hints g)

  test₃ : ∀ {n} → Even n → Even (n + 2)
  test₃ = quoteGoal g in unquote (auto 5 hints g)

-- This test should not type check
--  testFail : ∀ {n} → Even n → Even (n + 3)
--  testFail = quoteGoal g in unquote (auto 5 hints g)

  