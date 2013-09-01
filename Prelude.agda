import Level
import Data.Colist using () renaming (Colist to CoList; [] to Nil; _∷_ to Cons)
import Data.Sum using () renaming (_⊎_ to Either; inj₁ to Inl; inj₂ to Inr)
import Data.Empty using () renaming (⊥ to Empty)
import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
import Data.List using (List; map; _++_) renaming ([] to Nil; _∷_ to Cons)
import Data.Maybe using (Maybe; functor) renaming (just to Just; nothing to Nothing)
import Data.Nat renaming (ℕ to Nat; zero to Zero; suc to Succ)
import Data.Vec using (Vec) renaming ([] to Nil; _∷_ to Cons; map to vmap)
import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _==_; _≢_ to _<>_; refl to Refl)

module Prelude where

  open Data.Colist public
  open Data.Sum public
  open Data.Empty public
  open Data.Fin public
  open Data.List public
  open Data.Maybe public
  open Data.Nat public
  open Data.Vec public
  open Relation.Binary.PropositionalEquality public

  _>>=_ : forall {ℓ} {A B : Set ℓ} -> Maybe A -> (A -> Maybe B) -> Maybe B
  Nothing >>= f = Nothing
  Just x  >>= f = f x

  _<*>_ : forall {ℓ} {A B : Set ℓ} -> Maybe (A -> B) -> Maybe A -> Maybe B
  Nothing <*> mx      = Nothing
  Just f  <*> Nothing = Nothing
  Just f  <*> Just x  = Just (f x)

  _<$>_ : forall {ℓ} {A B : Set ℓ} -> (A -> B) -> Maybe A -> Maybe B
  f <$> Nothing = Nothing
  f <$> Just x  = Just (f x)

  record ∃ {ℓ} {A : Set ℓ} (P : A -> Set ℓ) : Set ℓ where
    constructor _,_
    field
      witness : A
      proof   : P witness
      
  thin : {n : Nat} -> Fin (Succ n) -> Fin n -> Fin (Succ n)
  thin Fz j = Fs j
  thin (Fs i) Fz = Fz
  thin (Fs i) (Fs j) = Fs (thin i j)

  thick : {n : Nat} -> (i j : Fin (Succ n)) -> Maybe (Fin n)
  thick Fz Fz = Nothing
  thick Fz (Fs i) = Just i
  thick {Zero} (Fs ()) j
  thick {Succ k} (Fs i) Fz = Just Fz
  thick {Succ k} (Fs i) (Fs j) = Fs <$> thick i j
