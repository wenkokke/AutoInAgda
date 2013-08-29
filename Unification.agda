open import Prelude hiding (_++_)

module Unification (A : Set) (arity : A -> Nat) (equal? : (x y : A) -> Either (x == y) (x <> y)) where

data Term (n : Nat) : Set where
  Var : (i : Fin n) -> Term n
  Con : (x : A) -> (xs : Vec (Term n) (arity x)) -> Term n

data Subst : (n m : Nat) -> Set where
  Nil : {n : Nat} -> Subst n n
  Cons : {n m : Nat} -> (i : Fin (Succ m)) -> (t : Term m) -> (subst : Subst m n) -> Subst (Succ m) n

empty : {n : Nat} -> ∃ (Subst n)
empty {n} = n , Nil

mutual
  replace : {n m : Nat} -> (Fin n -> Term m) -> Term n -> Term m
  replace f (Var i) = f i
  replace f (Con x xs) = Con x (replaceChildren f xs)

  replaceChildren : {n m k : Nat} -> (Fin n -> Term m) -> Vec (Term n) k -> Vec (Term m) k
  replaceChildren f Nil = Nil
  replaceChildren f (Cons x xs) = Cons (replace f x) (replaceChildren f xs)

_⋄_ : {k n m : Nat} -> (Fin m -> Term n) -> (Fin k -> Term m) -> Fin k -> Term n
_⋄_ f g i = replace f (g i)

mutual
  check : {n : Nat} -> (i : Fin (Succ n)) -> (t : Term (Succ n)) -> Maybe (Term n)
  check i (Var j) = Var <$> thick i j
  check i (Con x xs) = Con x <$> checkChildren i xs

  checkChildren : {n k : Nat} -> (i : Fin (Succ n)) -> (ts : Vec (Term (Succ n)) k) -> Maybe (Vec (Term n) k)
  checkChildren i Nil = Just Nil
  checkChildren i (Cons x xs) = check i x >>= \t ->
                                checkChildren i xs >>= \ts ->
                                Just (Cons t ts)


_for_ : {n : Nat} -> (t : Term n) -> (i j : Fin (Succ n)) -> Term n
_for_ t' i j with thick i j
_for_ t' i j | Nothing = t'
_for_ t' i j | Just x = Var x


apply : {n m : Nat} -> Subst n m -> Fin n -> Term m
apply Nil = Var
apply (Cons i t subst) = apply subst ⋄ (t for i)

_++_ : {n m k : Nat} -> Subst n m -> Subst m k -> Subst n k
Nil ++ subst' = subst'
Cons i t subst ++ subst' = Cons i t (subst ++ subst')

flexRigid : {n : Nat} -> Fin n -> Term n -> Maybe (∃ (Subst n))
flexRigid {Zero} () t
flexRigid {Succ k} i t with check i t
flexRigid {Succ k} i t | Nothing = Nothing
flexRigid {Succ k} i t | Just x = Just (k , (Cons i x Nil))

flexFlex : {n : Nat} -> (i j : Fin n) -> ∃ (Subst n)
flexFlex {Zero} () j
flexFlex {Succ k} i j with thick i j
flexFlex {Succ k} i j | Nothing = ((Succ k) , Nil)
flexFlex {Succ k} i j | Just x = (k , Cons i (Var x) Nil)

mutual
  unifyAcc : {m : Nat} -> (s t : Term m) -> ∃ (Subst m) -> Maybe (∃ (Subst m))
  unifyAcc (Con  x xs) (Con y ys) acc with equal? x y
  unifyAcc (Con .y xs) (Con y ys) acc | Inl Refl = unifyChildren xs ys acc
  unifyAcc (Con  x xs) (Con y ys) acc | Inr y' = Nothing
  unifyAcc (Var i) (Var j) (k , Nil) = Just (flexFlex i j)
  unifyAcc (Var i) t (k , Nil) = flexRigid i t
  unifyAcc t (Var j) (k , Nil) = flexRigid j t
  unifyAcc s t (k , Cons i t' subst) =
    (\s -> (∃.witness s) , (Cons i t' (∃.proof s)))
      <$> unifyAcc (replace (t' for i) s) (replace (t' for i) t) (k , subst)

  unifyChildren : {n k : Nat} -> (xs ys : Vec (Term n) k) -> ∃ (Subst n) -> Maybe (∃ (Subst n))
  unifyChildren Nil Nil acc = Just acc
  unifyChildren (Cons x xs) (Cons y ys) acc = unifyAcc x y acc >>= unifyChildren xs ys

unify  : {m : Nat} -> (s t : Term m) -> Maybe (∃ (Subst m))
unify {m} s t = unifyAcc s t (m , Nil)
