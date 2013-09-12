open import Prelude
open import Coinduction renaming (♯_ to Thunk; ♭ to Force)

module Prolog (A : Set) (arity : A → ℕ) (equal? : (x y : A) → Either (x == y) (x <> y)) where

import Unification

module UnificationInstance = Unification A arity equal?
open UnificationInstance public hiding (_++_)


-- A 'coinductive' list monad

data Search (A : Set) : Set where
  Fail   : Search A
  Return : A → Search A
  Fork   : ∞ (Search A) → ∞ (Search A) → Search A

-- The Term language

Goal : ℕ → Set
Goal n = Term n


-- Prolog rules

record Rule (n : ℕ) : Set where
  constructor _:-_
  field
    conclusion : Term n
    premises : List (Term n)


Rules : ℕ → Set
Rules n = List (Rule n)

rule : {n : ℕ} → Term n → List (Term n) → Rule n
rule t ts = record { conclusion = t; premises = ts }

axiom : {n : ℕ} → Term n → Rule n
axiom t = rule t []


-- Constructing the search tree and dfs

data SearchTree (n : ℕ) : Set where
  Done : (subst : ∃ (Subst n)) → SearchTree n
  Step : (Rule n → ∞ (SearchTree n)) → Rules n → SearchTree n

fail : {n : ℕ} → SearchTree n
fail = Step (\_ → Thunk fail) []

dfs : {n : ℕ} → SearchTree n → Search (∃ (Subst n))
dfs (Done subst) = Return subst
dfs (Step f []) = Fail
dfs (Step f (x ∷ xs)) = Fork (Thunk (dfs (Force (f x)))) (Thunk (dfs (Step f xs)))

-- The resolution algorithm

solve : {n : ℕ} → Rules n → Goal n → SearchTree n
solve {n} rules goal = go (Just empty) (goal ∷ [])
  where
  go : Maybe (∃ (Subst n)) → List (Goal n) → SearchTree n
  go Nothing xs = fail
  go (Just x) [] = Done x
  go subst (goal ∷ goals) =
    Step (λ r → Thunk (go (subst >>= unifyAcc goal (Rule.conclusion r)) (goals ++ Rule.premises r))) rules

-- Searching until a fixed depth

dfsToDepth : {a : Set} → ℕ → Search a → List a
dfsToDepth  zero    xs          = []
dfsToDepth (suc k)  Fail        = []
dfsToDepth (suc k) (Return x)   = x ∷ []
dfsToDepth (suc k) (Fork xs ys) = (dfsToDepth k (Force xs)) ++ (dfsToDepth k (Force ys))


-- Correctness proof

data In {a : Set} (x : a) : List a → Set where
  Top : forall {xs} → In x (x ∷ xs)
  Pop : forall {y xs} → In x xs → In x (y ∷ xs)

data Forall {a : Set} (P : a → Set) : List a → Set where
  Done : Forall P []
  Step : forall {x xs} → P x → Forall P xs → Forall P (x ∷ xs)

data Proof {n : ℕ} (rules : Rules n) (t : Term n)  : Set where
  Axiom : In (axiom t) rules → Proof rules t
  Apply : forall {ps} → In (rule t ps) rules → Forall (Proof rules) ps → Proof rules t
