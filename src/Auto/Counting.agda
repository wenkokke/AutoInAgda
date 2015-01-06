open import Auto.Core                  using (Rule; RuleName; _≟-RuleName_; name2rule; IsHintDB)
open import Level                      using (zero)
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


--------------------------------------------------------------------------------
-- Define a 'counting' hint database which, upon selection of a rule will     --
-- decrement an associated 'count' value, and upon reaching 0 will delete     --
-- the hint from the hint database.                                           --
--                                                                            --
-- The count values can either be natural numbers, in which case they         --
-- will be decremented as expected, or the value ⊤, in which case they        --
-- will not be decremented, effectively inserting infinite copies of the      --
-- rule into the hint database.                                               --
--------------------------------------------------------------------------------

module CountingHintDB where

  open RawFunctor (Maybe.functor {zero}) using (_<$>_)

  Count : Set
  Count = ℕ ⊎ ⊤
  
  record Hint (k : ℕ) : Set where
    constructor mkHint
    field
      rule  : Rule k
      count : Count
  
    ruleName : RuleName
    ruleName = Rule.name rule

  HintDB : Set
  HintDB = List (∃ Hint)
  
  decrCount : ∀ {k} → Hint k → Maybe (Hint k)
  decrCount {k} (mkHint r c) = mkHint r <$> decrCount′ c 
    where
      decrCount′ : Count → Maybe Count
      decrCount′ (inj₁ 0) = nothing
      decrCount′ (inj₁ 1) = nothing
      decrCount′ (inj₁ x) = just (inj₁ (pred x))
      decrCount′ (inj₂ _) = just (inj₂ _)

  getTr : ∀ {k} → Hint k → (HintDB → HintDB)
  getTr h₁ = List.concatMap (List.fromMaybe ∘ mdecr₁)
    where
      mdecr₁ : ∃ Hint → Maybe (∃ Hint)
      mdecr₁ (_ , h₂) =
        if ⌊ Hint.ruleName h₁ ≟-RuleName Hint.ruleName h₂ ⌋
        then (_,_ _) <$> decrCount h₂
        else just (_ , h₂)
    
  countingHintDB : IsHintDB
  countingHintDB = record
    { HintDB   = HintDB
    ; Hint     = Hint
    ; getHints = id
    ; getRule  = Hint.rule
    ; getTr    = getTr
    ; ε        = []
    ; _∙_      = _++_
    ; return   = λ r → [ _ , mkHint r (inj₂ _) ]
    }



open CountingHintDB using (mkHint; countingHintDB)
open import Auto.Extensible countingHintDB public renaming (auto to countingAuto)



--------------------------------------------------------------------------------
-- Define some new syntax in order to insert rules with limited usage.        --
--------------------------------------------------------------------------------

infixl 5 _<<[_]_

_<<[_]_ : HintDB → ℕ → Name → HintDB
db <<[ 0 ] _ = db
db <<[ x ] n with (name2rule n)
db <<[ x ] n | inj₁ msg     = db
db <<[ x ] n | inj₂ (k , r) = db ∙ [ k , mkHint r (inj₁ x) ]

