import Unification
open import Function using (id; const; flip; _∘_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Functor
open import Category.Monad
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Colist using (Colist; []; _∷_)
open import Data.List as List using (List; []; _∷_; _++_; map)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong)

module Prolog (Sym : ℕ → Set) (decEqSym : ∀ {k} (f g : Sym k) → Dec (f ≡ g)) where

  module UI = Unification Sym decEqSym
  open UI public hiding (_++_)

  -- | possibly infinite search tree with suspended computations
  data Search (A : Set) : Set where
    fail   : Search A
    return : A → Search A
    fork   : ∞ (Search A) → ∞ (Search A) → Search A

  -- | encoding of prolog-style rules indexed by their number of variables
  record Rule (n : ℕ) : Set where
    constructor _:-_
    field
      conclusion : Term n
      premises   : List (Term n)

  open Rule using (conclusion; premises)

  -- | alias for lists of rules
  Rules : Set
  Rules = List (∃ Rule)

  -- | alias for term to clarify its semantics
  Goal : ℕ → Set
  Goal n = Term n

  -- | injects a Finᵐ into the lower half of Finᵐ⁺ⁿ
  injectᴸ : {m : ℕ} → (n : ℕ) → Fin m → Fin (m + n)
  injectᴸ {zero}  _  ()
  injectᴸ {suc m} _  zero   = zero
  injectᴸ {suc m} _ (suc i) = suc (injectᴸ {m} _ i)

  -- | injects a Finⁿ into the upper half of Finᵐ⁺ⁿ
  injectᴿ : (m : ℕ) → {n : ℕ} → Fin n → Fin (m + n)
  injectᴿ  zero   {zero}   ()
  injectᴿ (suc m) {zero}   ()
  injectᴿ  zero   {suc n}  zero    = zero
  injectᴿ  zero   {suc n} (suc i) = suc (injectᴿ 0 {n} i)
  injectᴿ (suc m) {suc n} i       = suc (injectᴿ m {suc n} i)

  raiseᴸ : {m : ℕ} → (n : ℕ) → Rule m → Rule (m + n)
  raiseᴸ {m} n (conc :- prem) = dn conc :- map dn prem
    where dn = replace (var ∘ injectᴸ {m} n)

  raiseᴿ : (m : ℕ) → {n : ℕ} → Rule n → Rule (m + n)
  raiseᴿ m {n} (conc :- prem) = up conc :- map up prem
    where up = replace (var ∘ injectᴿ m {n})

  -- | unifies two rules after raising their domain to include all
  --   needed free variables
  join : List (∃ Rule) → ∃ (List ∘ Rule)
  join [] = zero , []
  join ((m , r) ∷ rs) with join rs
  ... | n , rs' = _ , raiseᴸ n r ∷ map (raiseᴿ m) rs'

  -- | constructing a search tree and performing depth-first search
  data SearchTree (n : ℕ) : Set where
    done : ∃ (Subst n) → SearchTree n
    step : (Rule n → ∞ (SearchTree n)) → List (Rule n) → SearchTree n

  loop : ∀ {n} → SearchTree n
  loop = step (λ _ → ~ loop) []

  solve : ∀ {m} → Rules → Goal m → ∃ SearchTree
  solve {m} rs g with join rs
  ... | n    , rs' with replace (var ∘ injectᴸ n) g | map (raiseᴿ m) rs'
  ... | goal | rules = mn , go (just (mn , nil)) (goal ∷ [])
    where
    mn = m + n
    go : Maybe (∃ (Subst mn)) → List (Goal mn) → SearchTree mn
    go nothing  _  = loop
    go (just s) [] = done s
    go (just s) (g ∷ gs) =
      step (λ r → ~ go (unifyAcc g (conclusion r) s) (gs ++ premises r)) rules

  dfs : ∀ {n} → SearchTree n → Search (∃ (Subst n))
  dfs (done s)          = return s
  dfs (step f [])       = fail
  dfs (step f (x ∷ xs)) = fork (~ dfs (! f x)) (~ dfs (step f xs))

  toDepth : ∀ {A} → ℕ → Search A → List A
  toDepth zero     _           = []
  toDepth (suc k)  fail        = []
  toDepth (suc k) (return x)   = x ∷ []
  toDepth (suc k) (fork xs ys) = toDepth k (! xs) ++ toDepth k (! ys)
