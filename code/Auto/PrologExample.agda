open import Data.Fin
open import Data.List
open import Data.String
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
open import Data.Product

module Auto.PrologExample where

data Arith : Set where
  Suc   : Arith
  Zero  : Arith
  Add   : Arith

decEqArith : (x y : Arith) → Dec (x ≡ y)
decEqArith Suc Suc = yes refl
decEqArith Suc Zero = no (λ ())
decEqArith Suc Add = no (λ ())
decEqArith Zero Suc = no (λ ())
decEqArith Zero Zero = yes refl
decEqArith Zero Add = no (λ ())
decEqArith Add Suc = no (λ ())
decEqArith Add Zero = no (λ ())
decEqArith Add Add = yes refl

--open import Unification Arith decEqArith as U
open import Prolog String Arith decEqArith


AddBase : Rule 1
AddBase = rule "AddBase" (con Add (con Zero [] ∷  var zero ∷  var zero ∷  [])) []
AddStep : Rule 3
AddStep = rule "AddStep" (con Add (con Suc (var (# 0) ∷ []) 
                                 ∷ var (# 1)         
                                 ∷ con Suc (var (# 1) ∷ [])
                                 ∷ []))
                         ((con Add (
                             (var zero
                             ∷  var (# 1)
                             ∷  var (# 2)
                             ∷ [])))
                        ∷ [])

rules : Rules
rules = (1 , AddBase) ∷ (3 , AddStep) ∷ []

one : PrologTerm 1
one = con Suc (con Zero [] ∷ [])

two : PrologTerm 1
two = con Suc (one ∷ [])

goal : PrologTerm 1
goal = con Add (one ∷ two ∷ var (# 0) ∷ [])

example = searchToDepth 10 rules goal
