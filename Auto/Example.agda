open import Auto
open import Function using (id; const)
open import Data.Bin as Bin using (Bin) renaming (0# to bin; toℕ to bin2nat)
open import Data.List as List using (List; _∷_; [])
open import Data.Nat.Show using () renaming (show to nat2str)
open import Data.String using (String)
open import Reflection using (Name)

module Auto.Example where

  hints : List Name
  hints = quote bin ∷ quote bin2nat ∷ quote nat2str ∷ []

  test : String
  test = quoteGoal g in unquote (auto 5 hints g)
