open import Function     using (const; id)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; name2rule)
open import Data.List    using ([]; [_]; _++_)
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Reflection   using (Name; Term; TC)

module Auto where

open import Auto.Extensible simpleHintDB public renaming (auto to auto′)

auto : ℕ → HintDB → Term → TC Term
auto = auto′ dfs

macro
  autoMacro = auto
