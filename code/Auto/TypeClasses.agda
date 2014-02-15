open import Auto
open import Algebra
open import Reflection
open import Data.Maybe
open import Data.List using (_∷_; [])
open import Data.String using (String; _++_)
-- open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Show using () renaming (show to showBool)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)

module Auto.TypeClasses where

record Show (A : Set) : Set where
  field
    show : A → String

open Show {{...}}

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

ShowProd : {A B : Set} → Show A → Show B -> Show (A × B)
ShowProd {A} {B} ShowA ShowB = record { show = showProd }
  where
    showProd : A × B -> String
    showProd (x , y) = "(" ++ show x ++ "," ++ show y ++ ")"

ShowBool : Show Bool
ShowBool = record { show = showBool }

Showℕ : Show ℕ
Showℕ = record { show = showℕ }

ShowHints : HintDB
ShowHints = hintdb (quote ShowProd ∷ quote ShowBool ∷ quote Showℕ ∷ [])

example : String
example = show (true , 5)
  where
    ShowInst = quoteGoal g in unquote (auto 5 ShowHints g)
