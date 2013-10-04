open import Algebra
open import Algebra.Structures
open import Function using (id; const; flip; _∘_; _$_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Functor
open import Category.Monad
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as NatProps using ()
open import Data.Fin using (Fin; suc; zero)
open import Data.Colist using (Colist; []; _∷_)
open import Data.List as List using (List; []; _∷_; _++_; map; concatMap; fromMaybe)
open import Data.Vec as Vec using (Vec; []; _∷_) renaming (map to vmap)
open import Data.Product using (∃; ∃₂; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)

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
  injectL _  zero   = zero
  injectL _ (suc i) = suc (injectL _ i)

  -- | injects a Finⁿ into the upper half of Finᵐ⁺ⁿ
  injectR : (m : ℕ) → {n : ℕ} → Fin n → Fin (m + n)
  injectR zero   i = i
  injectR (suc m) i = suc (injectR m i)

  -- | injects a Termᵐ into the lower half of Termᵐ⁺ⁿ
  injectTermL : {m : ℕ} → (n : ℕ) → Term m → Term (m + n)
  injectTermL n = replace (var ∘ injectL n)

  -- | injects a Termⁿ into the upper half of Termᵐ⁺ⁿ
  injectTermR : (m : ℕ) → {n : ℕ} → Term n → Term (m + n)
  injectTermR m = replace (var ∘ injectR m)

  -- | injects a Ruleᵐ into the lower half of Ruleᵐ⁺ⁿ
  injectRuleL : {m : ℕ} → (n : ℕ) → Rule m → Rule (m + n)
  injectRuleL {m} n (conc :- prem) = inj conc :- map inj prem
    where inj = injectTermL n

  -- | injects a Ruleⁿ into the upper half of Ruleᵐ⁺ⁿ
  injectRuleR : (m : ℕ) → {n : ℕ} → Rule n → Rule (m + n)
  injectRuleR m {n} (conc :- prem) = inj conc :- map inj prem
    where inj = injectTermR m

  -- | injects a Substᵐⁿ into the lower half of Subst⁽ᵐ⁺ᵉ⁾⁽ⁿ⁺ᵉ⁾
  injectSubstL : ∀ {m n} (ε : ℕ) → Subst m n → Subst (m + ε) (n + ε)
  injectSubstL _ nil = nil
  injectSubstL ε (snoc s t x) = snoc (injectSubstL ε s) (injectTermL ε t) (injectL ε x)

  -- Search Trees
  --
  -- What can we guarantee about the final `Subst m n`?
  --
  -- * Not the upper bound of m, as this depends on the number of rule
  --   applications we use and which rules we use, and thus not the upper
  --   bound of n, as this depends on that of m; but
  --
  -- * We can guarantee the lower bound of m, as it should be at least
  --   equal to the number of variables in the initial goal.
  --
  -- * Ideally we would be able to guarantee that after a proof search the
  --   n is always equal to 0.

  data SearchTree (m : ℕ) : Set where
    done : ∃₂ (λ n ε → Subst (m + ε) (n + ε)) → SearchTree m
    step : (∃ Rule → ∞ (SearchTree m)) → Rules → SearchTree m

  loop : ∀ {m} → SearchTree m
  loop = step (λ _ → ~ loop) []

  solve : ∀ {m} → Rules → Goal m → SearchTree m
  solve {m} rules goal = {!!}
    where
    solveAcc : ∀ {m ε} → Maybe (∃ (λ n → Subst (m + ε) (n + ε))) → List (Goal (m + ε)) → SearchTree m
    solveAcc {m} {ε} nothing _ = loop
    solveAcc {m} {ε} (just (n , s)) [] = done (n , ε , s)
    solveAcc {m} {ε} (just (n , s)) (g ∷ gs) = step next rules
      where
      next : ∃ Rule → ∞ (SearchTree m)
      next (δ , r) = ~ solveAcc {m} {ε + δ} mgu (gs' ++ prm)
        where

        open CommutativeSemiring NatProps.commutativeSemiring using (+-assoc)

        -- unifyAcc : ∀ {m ε} (t₁ t₂ : Term (m + ε))
        --            → ∃ (λ n → Subst (m + ε) (n + ε))
        --            → Maybe (∃ (λ n → Subst (m + ε) (n + ε)))

        mgu : Maybe (∃ (λ n → Subst (m + (ε + δ)) (n + (ε + δ))))
        mgu = {!!}

        -- | subgoals lifted to (m + ε + δ)
        gs' : List (Term (m + (ε + δ)))
        gs' rewrite sym (+-assoc m ε δ) = map (injectTermL δ) gs

        -- | premises for the chosen rule lifted to (m + ε + δ)
        prm : List (Term (m + (ε + δ)))
        prm rewrite sym (+-assoc m ε δ) = map (injectTermR (m + ε)) (premises r)




  {-
  solve : ∀ {m} → Rules → Goal m → SearchTree
  solve {m} rs g with joinRules rs
  ... | n    , rs' with raiseGoalL g | map (raiseRuleR m) rs'
  ... | goal | rules = m + n , solveAcc (just (m + n , nil)) (goal ∷ [])
    where
    solveAcc : Maybe (∃ (Subst (m + n))) → List (Goal (m + n)) → SearchTree (m + n)
    solveAcc nothing  _  = loop
    solveAcc (just s) [] = done s
    solveAcc (just s) (g ∷ gs) =
      step (λ r → ~ solveAcc (unifyAcc g (conclusion r) s) (gs ++ premises r)) rules
  -}

  dfs : ∀ {m} → SearchTree m → Search (∃₂ (λ n ε → Subst (m + ε) (n + ε)))
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
