open import Auto.Core  using (defaultHintDB; name2rule; dfs)
open import Data.List  using ([_]; _++_)
open import Data.Nat   using (ℕ)
open import Data.Sum   using (inj₁; inj₂)
open import Reflection using (Name; Term)

module Auto where

open import Auto.Extensible defaultHintDB public renaming (auto to simpleAuto′)



simpleAuto : ℕ → HintDB → Term → Term
simpleAuto = simpleAuto′ dfs



infixl 5 _<<_

_<<_ : HintDB → Name → HintDB
db << n with name2rule n
db << n | inj₁ msg = db
db << n | inj₂ r   = db ++ [ r ]
