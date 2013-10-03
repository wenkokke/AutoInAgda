open import Function using (id; const; flip; _∘_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Functor
open import Category.Monad
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Colist using (Colist; []; _∷_)
open import Data.List as List using (List; []; _∷_; _++_; map; concatMap; fromMaybe)
open import Data.Vec as Vec using (Vec; []; _∷_) renaming (map to vmap)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong)

module Prolog (Sym : ℕ → Set) (decEqSym : ∀ {k} (f g : Sym k) → Dec (f ≡ g)) where

  open RawMonad {{...}} renaming (return to mreturn)
  maybeMonad = Maybe.monad

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
  injectL : {m : ℕ} → (n : ℕ) → Fin m → Fin (m + n)
  injectL {zero}  _  ()
  injectL {suc m} _  zero   = zero
  injectL {suc m} _ (suc i) = suc (injectL {m} _ i)

  -- | injects a Finⁿ into the upper half of Finᵐ⁺ⁿ
  injectR : (m : ℕ) → {n : ℕ} → Fin n → Fin (m + n)
  injectR  zero   {zero}   ()
  injectR (suc m) {zero}   ()
  injectR  zero   {suc n}  zero    = zero
  injectR  zero   {suc n} (suc i) = suc (injectR 0 {n} i)
  injectR (suc m) {suc n} i       = suc (injectR m {suc n} i)

  -- | raises the domain of a Ruleᵐ into the lower half of Ruleᵐ⁺ⁿ
  raiseRuleL : {m : ℕ} → (n : ℕ) → Rule m → Rule (m + n)
  raiseRuleL {m} n (conc :- prem) = down conc :- map down prem
    where down = replace (var ∘ injectL {m} n)

  -- | raises the domain of a Ruleⁿ into the upper half of Ruleᵐ⁺ⁿ
  raiseRuleR : (m : ℕ) → {n : ℕ} → Rule n → Rule (m + n)
  raiseRuleR m {n} (conc :- prem) = up conc :- map up prem
    where up = replace (var ∘ injectR m {n})

  -- | raises the domain of a Goalᵐ into the lower half of Goalᵐ⁺ⁿ
  raiseGoalL : ∀ {m n} → Goal m → Goal (m + n)
  raiseGoalL {_} {n} = replace (var ∘ injectL n)

  -- | raises a list of rules of various domains to a list of rules
  --   over a unified domain
  joinRules : List (∃ Rule) → ∃ (List ∘ Rule)
  joinRules [] = zero , []
  joinRules ((m , r) ∷ rs) with joinRules rs
  ... | n , rs' = _ , raiseRuleL n r ∷ map (raiseRuleR m) rs'

  -- | constructing a search tree and performing depth-first search
  data SearchTree (n : ℕ) : Set where
    done : ∃ (Subst n) → SearchTree n
    step : (Rule n → ∞ (SearchTree n)) → List (Rule n) → SearchTree n

  loop : ∀ {n} → SearchTree n
  loop = step (λ _ → ~ loop) []

  solve : ∀ {m} → Rules → Goal m → ∃ SearchTree
  solve {m} rs g with joinRules rs
  ... | n    , rs' with raiseGoalL g | map (raiseRuleR m) rs'
  ... | goal | rules = m + n , solveAcc (just (m + n , nil)) (goal ∷ [])
    where
    solveAcc : Maybe (∃ (Subst (m + n))) → List (Goal (m + n)) → SearchTree (m + n)
    solveAcc nothing  _  = loop
    solveAcc (just s) [] = done s
    solveAcc (just s) (g ∷ gs) =
      step (λ r → ~ solveAcc (unifyAcc g (conclusion r) s) (gs ++ premises r)) rules

  {-
  dfs : ∀ {n} → SearchTree n → Search (∃ (Subst n))
  dfs (done s)          = return s
  dfs (step f [])       = fail
  dfs (step f (x ∷ xs)) = fork (~ dfs (! f x)) (~ dfs (step f xs))

  dfsToDepth : ∀ {A} → ℕ → Search A → List A
  dfsToDepth zero     _           = []
  dfsToDepth (suc k)  fail        = []
  dfsToDepth (suc k) (return x)   = x ∷ []
  dfsToDepth (suc k) (fork xs ys) = dfsToDepth k (! xs) ++ dfsToDepth k (! ys)
  -}

  dom : ∀ {n} → Vec (Fin n) n
  dom {zero}  = []
  dom {suc n} = zero ∷ vmap (injectR 1) (dom {n})

  -- while we should be able to guarantee that the terms after substitution
  -- contain no variables (and all free variables in the domain occur because
  -- of unused rules), the required proof of this is currently still unimplemented
  -- therefore, we have to resort to using maybe

  {-
  mutual
    noVars : ∀ {n} → Term n → Maybe (Term 0)
    noVars (var x)    = nothing
    noVars (con s ts) = con s <$> noVarsChildren ts

    noVarsChildren : ∀ {n k} → Vec (Term n) k → Maybe (Vec (Term 0) k)
    noVarsChildren [] = just []
    noVarsChildren (t ∷ ts) = noVars t >>= λ t' →
                              noVarsChildren ts >>= λ ts' →
                              mreturn (t' ∷ ts')

  filterWithVars : ∀ {m} → List (∃ (λ n → Vec (Term n) m)) → List (Vec (Term 0) m)
  filterWithVars = concatMap (fromMaybe ∘ noVarsChildren ∘ proj₂)

  solveToDepth : ∀ {m} (depth : ℕ) → Rules → Goal m → List (∃ (λ n → Vec (Term n) m))
  solveToDepth {m} depth rules goal = map app subs
    where
    vars : Vec (Fin m) m
    vars = dom
    tree = solve rules goal
    subs = dfsToDepth depth (dfs (proj₂ tree))
    app : ∃ (Subst (m + _)) → ∃ (λ n → Vec (Term n) m)
    app (n , s) = n , vmap (λ v → apply s v ) (vmap (injectL _) vars)
  -}
