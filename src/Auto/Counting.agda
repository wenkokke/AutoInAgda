open import Auto.Core                  using (Rule; RuleName; _≟-RuleName_; name2rule; IsHintDB)
open import Level
open import Function                   using (id; _∘_)
open import Category.Functor           using (module RawFunctor)
open import Data.Bool    as Bool       using (if_then_else_)
open import Data.List    as List       using (List; _++_; []; [_])
open import Data.Maybe   as Maybe      using (Maybe; just; nothing)
open import Data.Nat     as Nat        using (ℕ; pred)
open import Data.Product as Prod       using (∃; _,_; proj₂)
open import Data.Sum     as Sum        using (_⊎_; inj₁; inj₂)
open import Data.Unit    as Unit       using (⊤)
open import Reflection                 using (Name)
open import Relation.Nullary.Decidable using (⌊_⌋)

module Auto.Counting where

private
  module Private where

    Count : Set
    Count = ℕ ⊎ ⊤

    maybePred : Count → Maybe Count
    maybePred (inj₁ 0) = nothing
    maybePred (inj₁ x) = just (inj₁ (pred x))
    maybePred (inj₂ _) = just (inj₂ _)
  
    record Hint (k : ℕ) : Set where
      constructor mkHint
      field
        getRule  : Rule k
        getCount : Count
  
      getRuleName : RuleName
      getRuleName = Rule.name getRule
  
    open Hint using (getRule; getCount; getRuleName)
    
    maybeDecr : ∀ {k} → Hint k → Maybe (Hint k)
    maybeDecr {k} (mkHint r c) = mkHint r <$> maybePred c 
      where
        open RawFunctor Maybe.functor using (_<$>_)

    HintDB : Set
    HintDB = List (∃ Hint)

    getTr : ∀ {k} → Hint k → (HintDB → HintDB)
    getTr h₁ = List.concatMap (List.fromMaybe ∘ decrIf1)
      where
        decrIf1 : ∃ Hint → Maybe (∃ Hint)
        decrIf1 (_ , h₂) =
          if ⌊ getRuleName h₁ ≟-RuleName getRuleName h₂ ⌋
          then (_,_ _) <$> maybeDecr h₂
          else just (_ , h₂)
          where
            open RawFunctor Maybe.functor using (_<$>_)
    
    instHintDB : IsHintDB
    instHintDB = record
      { HintDB   = HintDB
      ; Hint     = Hint
      ; getHints = id
      ; getRule  = getRule
      ; getTr    = getTr
      ; ε        = List.[]
      ; _∙_      = List._++_
      ; fromRule = λ {k} r → List.[ k , mkHint r (inj₂ _) ]
      }



open Private using (mkHint; instHintDB)
open import Auto.Extensible instHintDB public renaming (auto to countingAuto)



infixl 5 _<<_ _<<[_]_

_<<_ : HintDB → Name → HintDB
db << n with (name2rule n)
db << n | inj₁ msg     = db
db << n | inj₂ (k , r) = db ∙ fromRule r

_<<[_]_ : HintDB → ℕ → Name → HintDB
db <<[ x ] n with (name2rule n)
db <<[ x ] n | inj₁ msg     = db
db <<[ x ] n | inj₂ (k , r) = db ∙ [ k , mkHint r (inj₁ x) ]

