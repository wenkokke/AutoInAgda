open import Function using (id; const; flip; _∘_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Functor
open import Category.Monad
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Colist using (Colist; []; _∷_)
open import Data.List as List using (List; []; _∷_; _++_; map)
open import Data.Vec as Vec using (Vec; []; _∷_) renaming (map to vmap)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong)

module Prolog (Sym : ℕ → Set) (decEqSym : ∀ {k} (f g : Sym k) → Dec (f ≡ g)) where

  import Unification
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

  -- | raises the domain of a `Rule m` into the lower half of `m + n`
  raiseRuleᴸ : {m : ℕ} → (n : ℕ) → Rule m → Rule (m + n)
  raiseRuleᴸ {m} n (conc :- prem) = down conc :- map down prem
    where down = replace (var ∘ injectᴸ {m} n)

  -- | raises the domain of a `Rule m` into the upper half of `m + n`
  raiseRuleᴿ : (m : ℕ) → {n : ℕ} → Rule n → Rule (m + n)
  raiseRuleᴿ m {n} (conc :- prem) = up conc :- map up prem
    where up = replace (var ∘ injectᴿ m {n})

  -- | raises the domain of a `Goal m` into the lower half of `m + n`
  raiseGoal : ∀ {m n} → Goal m → Goal (m + n)
  raiseGoal {_} {n} = replace (var ∘ injectᴸ n)

  -- | raises a list of rules of various domains to a list of rules
  --   over a unified domain
  joinRules : List (∃ Rule) → ∃ (List ∘ Rule)
  joinRules [] = zero , []
  joinRules ((m , r) ∷ rs) with joinRules rs
  ... | n , rs' = _ , raiseRuleᴸ n r ∷ map (raiseRuleᴿ m) rs'

  -- | constructing a search tree and performing depth-first search
  data SearchTree (n : ℕ) : Set where
    done : ∃ (Subst n) → SearchTree n
    step : (Rule n → ∞ (SearchTree n)) → List (Rule n) → SearchTree n

  loop : ∀ {n} → SearchTree n
  loop = step (λ _ → ~ loop) []

  solve : ∀ {m} → Rules → Goal m → ∃ SearchTree
  solve {m} rs g with joinRules rs
  ... | n    , rs' with raiseGoal g | map (raiseRuleᴿ m) rs'
  ... | goal | rules = m + n , solveAcc (just (m + n , nil)) (goal ∷ [])
    where
    solveAcc : Maybe (∃ (Subst (m + n))) → List (Goal (m + n)) → SearchTree (m + n)
    solveAcc nothing  _  = loop
    solveAcc (just s) [] = done s
    solveAcc (just s) (g ∷ gs) =
      step (λ r → ~ solveAcc (unifyAcc g (conclusion r) s) (gs ++ premises r)) rules

  dfs : ∀ {n} → SearchTree n → Search (∃ (Subst n))
  dfs (done s)          = return s
  dfs (step f [])       = fail
  dfs (step f (x ∷ xs)) = fork (~ dfs (! f x)) (~ dfs (step f xs))

  dfsToDepth : ∀ {A} → ℕ → Search A → List A
  dfsToDepth zero     _           = []
  dfsToDepth (suc k)  fail        = []
  dfsToDepth (suc k) (return x)   = x ∷ []
  dfsToDepth (suc k) (fork xs ys) = dfsToDepth k (! xs) ++ dfsToDepth k (! ys)

  dom : ∀ {n} → Vec (Fin n) n
  dom {zero}  = []
  dom {suc n} = zero ∷ vmap (injectᴿ 1) (dom {n})

  solveToDepth : ∀ {m} (depth : ℕ) → Rules → Goal m → List (Vec (∃ Term) m)
  solveToDepth {m} depth rules goal = map app subs
    where
    vars : Vec (Fin m) m
    vars = dom
    tree = solve rules goal
    subs = dfsToDepth depth (dfs (proj₂ tree))
    app : ∃ (Subst (m + _)) → Vec (∃ Term) m
    app (n , s) = vmap (λ v → n , apply s v ) (vmap (injectᴸ _) vars)
