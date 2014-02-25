open import Function using (_∘_; _$_; flip; id)
open import Coinduction
open import Category.Monad
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Vec using (Vec; []; _∷_; toList) renaming (map to vmap)
open import Data.List using (List; []; _∷_; intersperse; map; foldr; foldl; reverse)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

module Prolog.Example where

  open RawMonad {{...}} renaming (return to mreturn)
  private maybeMonad = Maybe.monad

  data Arith : Set where
    Add  : Arith
    Suc  : Arith
    Zero : Arith

  decEqArith : (x y : Arith) → Dec (x ≡ y)
  decEqArith Add  Add  = yes refl
  decEqArith Add  Suc  = no (λ ())
  decEqArith Add  Zero = no (λ ())
  decEqArith Suc  Add  = no (λ ())
  decEqArith Suc  Suc  = yes refl
  decEqArith Suc  Zero = no (λ ())
  decEqArith Zero Add  = no (λ ())
  decEqArith Zero Suc  = no (λ ())
  decEqArith Zero Zero = yes refl

  open import Prolog String Arith decEqArith renaming (PrologTerm to Term)

  One   : Term 0
  One   = con Suc (con Zero [] ∷ [])
  Two   : Term 0
  Two   = con Suc (One ∷ [])
  Three : Term 0
  Three = con Suc (Two ∷ [])
  Four  : Term 0
  Four  = con Suc (Three ∷ [])

  X : Term 1
  X = var (# 0)

  Three+One? : Term 1
  Three+One? = con Add (injectTerm 1 Three ∷ injectTerm 1 One ∷ X ∷ [])

  AddBase : Rule 1
  AddBase = record
    { name        = "AddBase"
    ; conclusion  = con Add  (con Zero [] ∷ var (# 0) ∷ var (# 0)  ∷ [])
    ; premises    = []
    }

  AddStep : Rule 3
  AddStep = record
    { name        = "AddStep"
    ; conclusion  = con Add (con Suc (var (# 0) ∷ []) ∷ var (# 1) ∷ con Suc (var (# 2) ∷ []) ∷ [])
    ; premises    = con Add (var (# 0) ∷ var (# 1) ∷ var (# 2) ∷ []) ∷ []
    }

  Expected : List (Term 0)
  Expected = Four ∷ []
  Actual   : List (Term 0)
  Actual   = map proj₁ (toResult X substs)
    where
      substs : List (Result 1)
      substs = searchToDepth 5 ((_ , AddBase) ∷ (_ , AddStep) ∷ []) Three+One?

  -- WARNING: THIS BECOMES AN INFINITE LOOP SOMEHOW
  test : Actual ≡ Expected
  test = {!refl!}

  -- DETAILS:
  --
  -- C-c C-t:
  --     con Suc (con Suc (con Suc (con Suc (con Zero [] ∷ []) ∷ []) ∷ []) ∷ []) ∷ []
  --   ≡ con Suc (con Suc (con Suc (con Suc (con Zero [] ∷ []) ∷ []) ∷ []) ∷ []) ∷ []
  --
  -- C-c C-SPC:
  --
  --     INFINITE LOOP
  --
