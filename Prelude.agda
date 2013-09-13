import Level
import Data.Colist using ([]; [_]; _∷_) renaming (Colist to CoList)
import Data.Sum using () renaming (_⊎_ to Either; inj₁ to Inl; inj₂ to Inr)
import Data.Empty using () renaming (⊥ to Empty)
import Data.Fin using (Fin; #_) renaming (zero to Fz; suc to Fs)
import Data.List using (List; map; _++_; []; _∷_)
import Data.Maybe using (Maybe; functor; monad) renaming (just to Just; nothing to Nothing)
import Data.Nat using (ℕ; zero; suc)
import Data.Vec using (Vec; []; _∷_) renaming (map to vmap)
import Data.Product using (∃; Σ; _,_) renaming (proj₁ to witness; proj₂ to proof)
import Relation.Nullary using (yes; no)
import Relation.Binary using (Decidable)
import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

module Prelude where

  open Data.Colist public
  open Data.Sum public
  open Data.Empty public
  open Data.Fin public
  open Data.List public
  open Data.Maybe public
  open Data.Nat public
  open Data.Vec public
  open Data.Product public
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

  thin : {n : ℕ} -> Fin (suc n) -> Fin n -> Fin (suc n)
  thin  Fz     j     = Fs j
  thin (Fs i)  Fz    = Fz
  thin (Fs i) (Fs j) = Fs (thin i j)

  thick : {n : ℕ} -> (i j : Fin (suc n)) -> Maybe (Fin n)
  thick          Fz      Fz    = Nothing
  thick          Fz     (Fs i) = Just i
  thick {zero}  (Fs ())  j
  thick {suc k} (Fs i)   Fz    = Just Fz
  thick {suc k} (Fs i)  (Fs j) = Fs <$> thick i j
