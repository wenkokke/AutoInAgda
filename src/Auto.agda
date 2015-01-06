open import Function     using (const; id)
open import Auto.Core    using (IsHintDB; Rules; Rule; name2rule; dfs)
open import Data.List    using ([]; [_]; _++_)
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Reflection   using (Name; Term)

module Auto where


simpleHintDB : IsHintDB
simpleHintDB = record
  { HintDB   = Rules
  ; Hint     = Rule
  ; getHints = id
  ; getRule  = id
  ; getTr    = const id
  ; ε        = []
  ; _∙_      = _++_
  ; return   = λ r → [ _ , r ]
  }


open import Auto.Extensible simpleHintDB public renaming (auto to simpleAuto′)

simpleAuto : ℕ → HintDB → Term → Term
simpleAuto = simpleAuto′ dfs

