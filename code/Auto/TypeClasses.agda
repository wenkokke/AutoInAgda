open import Auto
open import Algebra
open import Reflection
open import Data.Maybe
open import Data.List using (_∷_; [])
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)

import Data.Nat.Show as Nat
import Data.Bool.Show as Bool

module Auto.TypeClasses where

record Show (A : Set) : Set where
  field
    show : A → String

open Show {{...}}

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

ShowEither : {A B : Set} -> Show A → Show B → Show (Either A B)
ShowEither {A} {B} ShowA ShowB = record { show = showEither }
  where
    showEither : Either A B -> String
    showEither (left x) = "left " ++ show x
    showEither (right y) = "right " ++ show y

ShowBool : Show Bool
ShowBool = record { show = Bool.show }

Showℕ : Show ℕ
Showℕ = record { show = Nat.show }

ShowHints : HintDB
ShowHints = hintdb
  (quote ShowEither ∷ quote ShowBool ∷ quote Showℕ ∷ [])

example₁ : String
example₁ = show (left true) ++ show (right 4)
  where
    ShowInst = quoteGoal g in unquote (auto 5 ShowHints g)


-- THIS WORKS! HOORAY!
module Pair1 where

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  ShowPair : ∀ {A B} → Show A → Show B → Show (A × B)
  ShowPair {A} {B} showA showB = record { show = showPair }
    where
      showPair : A × B -> String
      showPair (proj₁ , proj₂) = show proj₁ ++ "," ++ show proj₂

  example₂ : String
  example₂ = show (true , 1)
    where
      ShowInst = quoteGoal g in unquote (auto 5 (ShowHints << quote ShowPair) g)


-- THIS BEHAVES STRANGELY DUE TO NORMALISATION
module Pair2 where

  open import Data.Product using (Σ; _,_)

  _×_ : (A B : Set) → Set
  A × B = Σ A (λ _ → B)

  ShowPair : {A B : Set} -> Show A → Show B → Show (A × B)
  ShowPair {A} {B} showA showB = record { show = showPair }
    where
      showPair : A × B -> String
      showPair (proj₁ , proj₂) = show proj₁ ++ "," ++ show proj₂

  example₂ : String
  example₂ = show (true , 5)
    where
      ShowInst = quoteGoal g in unquote (auto 5 (ShowHints << ShowPair) g)
