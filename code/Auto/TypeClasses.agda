open import Auto
open import Algebra
open import Reflection
open import Data.Maybe
open import Data.List using (_∷_; [])
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Show using () renaming (show to showBool)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)

module Auto.TypeClasses where

record Show (A : Set) : Set where
  field
    show : A → String

open Show {{...}}

data Either (A B : Set) : Set where
  Inl : A -> Either A B
  Inr : B -> Either A B

ShowEither : {A B : Set} -> Show A → Show B → Show (Either A B)
ShowEither {A} {B} ShowA ShowB = record { show = showEither }
  where
    showEither : Either A B -> String
    showEither (Inl x) = "Inl " ++ show x
    showEither (Inr y) = "Inr " ++ show y

ShowPair : {A B : Set} -> Show A → Show B → Show (A × B)
ShowPair {A} {B} showA showB = record { show = showPair }
  where
  showPair : A × B -> String
  showPair (proj₁ , proj₂) = show proj₁ ++ "," ++ show proj₂

ShowBool : Show Bool
ShowBool = record { show = showBool }

Showℕ : Show ℕ
Showℕ = record { show = showℕ }

ShowHints : HintDB
ShowHints = hintdb
  quote ShowEither ∷ quote ShowBool ∷ quote Showℕ ∷ quote ShowPair ∷ []



silly = show 3

example : String
example = show (true , true)
  where
    ShowInst : Show (Bool × Bool)
    ShowInst = quoteGoal g in unquote (auto 7 ShowHints g)


