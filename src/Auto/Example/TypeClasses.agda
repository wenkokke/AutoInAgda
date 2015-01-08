open import Auto
open import Data.Maybe
open import Data.List using (_∷_; [])
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Show as Bool using ()
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show as Nat using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum renaming (_⊎_ to Either; inj₁ to left; inj₂ to right)

module Auto.Example.TypeClasses where

--------------------------------------------------------------------------------
-- * We can construct a class for the Show function (as a dependent record) * --
--------------------------------------------------------------------------------

record Show (A : Set) : Set where
  constructor mkShow
  field
    show : A → String

open Show {{...}}


--------------------------------------------------------------------------------
-- * And set up a list of rules which guide the instance resolution         * --
--------------------------------------------------------------------------------

rules : HintDB
rules = [] << quote instShowEither << quote instShowBool << quote instShowNat
  where
    instShowBool : Show Bool
    instShowBool = mkShow Bool.show
    
    instShowNat : Show ℕ
    instShowNat = mkShow Nat.show
    
    instShowEither : {A B : Set} → Show A → Show B → Show (Either A B)
    instShowEither {A} {B} instShowA instShowB = mkShow showEither
      where
        showEither : Either A B → String
        showEither (left  x) = "left "  ++ show x
        showEither (right y) = "right " ++ show y



--------------------------------------------------------------------------------
-- * Using these rules and `auto` we can easily and robustly compute the    * --
-- * instances we need.                                                     * --
--------------------------------------------------------------------------------

example₁ : String
example₁ = show (left true) ++ show (right 4)
  where
    instance
      inst : Show (Either Bool ℕ)
      inst = tactic (auto 5 rules)



--------------------------------------------------------------------------------
-- * This fails due to normalisation from the non-dependent pair _×_ to the * --
-- * dependent pair Σ (as `A × B` is defined as `Σ A (λ _ → B)`).           * --
--------------------------------------------------------------------------------
module DefaultPair where

  open import Data.Product using (_×_; _,_)  

  instShowPair : {A B : Set} → Show A → Show B → Show (A × B)
  instShowPair {A} {B} showA showB = record { show = showPair }
    where
      showPair : A × B → String
      showPair (proj₁ , proj₂) = show proj₁ ++ "," ++ show proj₂

  inst : Exception unsupportedSyntax
  inst = unquote (auto 5 (rules << quote instShowPair) g)
    where
      g = quoteTerm (Show (Bool × ℕ))
  
      

--------------------------------------------------------------------------------
-- * So we're forced to use a custom pair, which isn't derived from         * --
-- * a dependent pair                                                       * --
--------------------------------------------------------------------------------
module CustomPair where

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  instShowPair : ∀ {A B} → Show A → Show B → Show (A × B)
  instShowPair {A} {B} showA showB = record { show = showPair }
    where
      showPair : A × B → String
      showPair (proj₁ , proj₂) = show proj₁ ++ "," ++ show proj₂

  example₂ : String
  example₂ = show (true , 1)
    where
      instance
        inst : Show (Bool × ℕ)
        inst = tactic (auto 5 (rules << quote instShowPair))



