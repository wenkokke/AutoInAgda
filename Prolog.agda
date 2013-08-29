open import Prelude
open import Coinduction renaming (♯_ to Thunk; ♭ to Force)

module Prolog (A : Set) (arity : A → Nat) (equal? : (x y : A) → Either (x == y) (x <> y)) where

import Unification

open module UnificationInstance = Unification A arity equal? using (Term; Subst; unifyAcc; empty)

-- A 'coinductive' list monad

data Search (A : Set) : Set where
  Fail   : Search A
  Return : A → Search A
  Fork   : ∞ (Search A) → ∞ (Search A) → Search A

[_] : {A : Set} → A → CoList A
[ x ] = Cons x (Thunk Nil)

[] : {A : Set} → CoList A
[] = Nil

-- The Term language

Goal : Nat → Set
Goal n = Term n

-- Prolog rules

record Rule (n : Nat) : Set where
  field
    conclusion : Term n
    premises : List (Term n)

Rules : Nat → Set
Rules n = List (Rule n)

rule : {n : Nat} → Term n → List (Term n) → Rule n
rule t ts = record { conclusion = t; premises = ts }

axiom : {n : Nat} → Term n → Rule n
axiom t = rule t Nil

-- Constructing the search tree and dfs

data SearchTree (n : Nat) : Set where
  Done : (subst : ∃ (Subst n)) → SearchTree n
  Step : (Rule n → ∞ (SearchTree n)) → Rules n → SearchTree n

fail : {n : Nat} → SearchTree n
fail = Step (\_ → Thunk fail) Nil

dfs : {n : Nat} → SearchTree n → Search (∃ (Subst n))
dfs (Done subst) = Return subst
dfs (Step f Nil) = Fail
dfs (Step f (Cons x xs)) = Fork (Thunk (dfs (Force (f x)))) (Thunk (dfs (Step f xs)))


-- The resolution algorithm

solve : {n : Nat} → Rules n → Goal n → SearchTree n
solve {n} rules goal = go (Just empty) (Cons goal Nil)
  where
  go : Maybe (∃ (Subst n)) → List (Goal n) → SearchTree n
  go Nothing xs = fail
  go (Just x) Nil = Done x
  go subst (Cons goal goals) =
    Step (λ r → Thunk (go (subst >>= unifyAcc goal (Rule.conclusion r)) (goals ++ Rule.premises r))) rules

-- Searching until a fixed depth

dfsToDepth : {a : Set} → Nat → Search a → List a
dfsToDepth Zero xs = Nil
dfsToDepth (Succ k) Fail = Nil
dfsToDepth (Succ k) (Return x) = Cons x Nil
dfsToDepth (Succ k) (Fork xs ys) = (dfsToDepth k (Force xs)) ++ (dfsToDepth k (Force ys))


-- Correctness proof
data In {a : Set} (x : a) : List a → Set where
  Top : forall {xs} → In x (Cons x xs)
  Pop : forall {y xs} → In x xs → In x (Cons y xs)

data Forall {a : Set} (P : a → Set) : List a → Set where
  Done : Forall P Nil
  Step : forall {x xs} → P x → Forall P xs → Forall P (Cons x xs)

data Proof {n : Nat} (rules : Rules n) (t : Term n)  : Set where
  Axiom : In (axiom t) rules → Proof rules t
  Apply : forall {ps} → In (rule t ps) rules → Forall (Proof rules) ps → Proof rules t
