open import Algebra
open import Algebra.Structures
open import Function using (id; const; flip; _∘_; _$_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Functor
open import Category.Monad
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as NatProps using ()
open import Data.Fin using (Fin; suc; zero)
open import Data.Colist using (Colist; []; _∷_)
open import Data.List as List using (List; []; _∷_; _∷ʳ_; _++_; map; foldr; concatMap; fromMaybe; length; take; drop)
open import Data.Vec as Vec using (Vec; []; _∷_; allFin) renaming (map to vmap)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂) renaming (map to pmap)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)

module Prolog (Name : Set) (Sym : ℕ → Set) (decEqSym : ∀ {k} (f g : Sym k) → Dec (f ≡ g)) where

  private
    open RawMonad {{...}}
    MonadMaybe = Maybe.monad
    MonadList  = List.monad
    open StrictTotalOrder NatProps.strictTotalOrder

  import Unification
  module UI = Unification Sym decEqSym
  open UI public using (Term; var; con)
  open UI using (Subst; snoc; nil; replace; apply; unifyAcc)


  -- | encoding of prolog-style rules indexed by their number of variables
  record Rule (n : ℕ) : Set where
    constructor rule
    field
      name       : Name
      conclusion : Term n
      premises   : List (Term n)

  open Rule public
       using (name; conclusion; premises)

  -- | compute the arity of a rule
  arity : ∀ {n} → Rule n → ℕ
  arity = length ∘ premises

  -- | alias for lists of rules
  Rules : Set
  Rules = List (∃ Rule)

  -- | alias for term to clarify its semantics
  Goal : ℕ → Set
  Goal n = Term n

  -- | injects a Finᵐ into the lower half of Finᵐ⁺ⁿ
  injectL : {m : ℕ} (n : ℕ) → Fin m → Fin (m + n)
  injectL _  zero   = zero
  injectL _ (suc i) = suc (injectL _ i)

  -- | injects a Finⁿ into the upper half of Finᵐ⁺ⁿ
  injectR : (m : ℕ) {n : ℕ} → Fin n → Fin (m + n)
  injectR zero   i = i
  injectR (suc m) i = suc (injectR m i)

  -- | injects a Termᵐ into the lower half of Termᵐ⁺ⁿ
  injectTermL : {m : ℕ} (n : ℕ) → Term m → Term (m + n)
  injectTermL n = replace (var ∘ injectL n)

  -- | injects a Termⁿ into the upper half of Termᵐ⁺ⁿ
  injectTermR : (m : ℕ) {n : ℕ} → Term n → Term (m + n)
  injectTermR m = replace (var ∘ injectR m)

  -- | injects a Ruleᵐ into the lower half of Ruleᵐ⁺ⁿ
  injectRuleL : {k : ℕ} {m : ℕ} (n : ℕ) → Rule m → Rule (m + n)
  injectRuleL {m} n (rule name conc prem) = rule name (inj conc) (map inj prem)
    where inj = injectTermL n

  -- | injects a Ruleⁿ into the upper half of Ruleᵐ⁺ⁿ
  injectRuleR : {k : ℕ} (m : ℕ) {n : ℕ} → Rule n → Rule (m + n)
  injectRuleR m {n} (rule name conc prem) = rule name (inj conc) (map inj prem)
    where inj = injectTermR m

  -- | injects a Substᵐⁿ into the lower half of Subst⁽ᵐ⁺ᵉ⁾⁽ⁿ⁺ᵉ⁾
  injectSubstL : ∀ {m n} (ε : ℕ) → Subst m n → Subst (m + ε) (n + ε)
  injectSubstL _ nil = nil
  injectSubstL ε (snoc s t x) = snoc (injectSubstL ε s) (injectTermL ε t) (injectL ε x)


  -- Abstract Search Trees
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
    done : ∃₂ (λ δ n → Subst (m + δ) n) → SearchTree m
    step : (∃ Rule → ∞ (SearchTree m)) → SearchTree m

  loop : ∀ {m} → SearchTree m
  loop = step (λ _ → ~ loop)

  solve : ∀ {m} → Goal m → SearchTree m
  solve {m} g = solveAcc {m} {0} (just (m , s₀)) (g₀ ∷ [])
    where
    open CommutativeSemiring NatProps.commutativeSemiring using (+-assoc; +-identity)

    -- small proofs that the initial domain (with room for m goal variables and
    -- 0 auxiliary variables) is equal to just the goal domain (with m variables)
    s₀ : Subst (m + 0) m
    s₀ rewrite proj₂ +-identity m = nil
    g₀ : Goal (m + 0)
    g₀ rewrite proj₂ +-identity m = g

    solveAcc : ∀ {m δ₁} → Maybe (∃ (λ n → Subst (m + δ₁) n)) → List (Goal (m + δ₁)) → SearchTree m
    solveAcc {m} {δ₁} nothing _ = loop
    solveAcc {m} {δ₁} (just (n , s)) [] = done (δ₁ , n , s)
    solveAcc {m} {δ₁} (just (n , s)) (g ∷ gs) = step next
      where
      next : ∃ Rule → ∞ (SearchTree m)
      next (δ₂ , r) = ~ solveAcc {m} {δ₁ + δ₂} mgu (prm ++ gs')
        where
        lem : (m + (δ₁ + δ₂)) ≡ ((m + δ₁) + δ₂)
        lem = sym (+-assoc m δ₁ δ₂)

        -- compute an mgu for the current sub-goal and the chosen rule
        mgu : Maybe (∃ (λ n → Subst (m + (δ₁ + δ₂)) n))
        mgu = unifyAcc g' cnc s'
          where

          -- lift arguments for unify into the new finite domain, making room for
          -- the variables used in the chosen rule.
          g'  : Term (m + (δ₁ + δ₂))
          g'  rewrite lem = injectTermL δ₂ g
          s'  : ∃ (Subst (m + (δ₁ + δ₂)))
          s'  rewrite lem = n + δ₂ , injectSubstL δ₂ s
          cnc : Term (m + (δ₁ + δ₂))
          cnc rewrite lem = injectTermR (m + δ₁) (conclusion r)

        -- lift arguments for the recursive call to solve into the new finite domain,
        -- making room for the variables used in the chosen rule.
        gs' : List (Term (m + (δ₁ + δ₂)))
        gs' rewrite lem = map (injectTermL δ₂) gs
        prm : List (Term (m + (δ₁ + δ₂)))
        prm rewrite lem = map (injectTermR (m + δ₁)) (premises r)


  -- Concrete Search Tree
  --
  -- A concrete search tree is a realization of an abstract search tree, by explicit
  -- branching and rule applications. Aside from applying each rule, the transformation
  -- from abstract to concrete also maintains a list of each applied rule.

  -- | possibly infinite search tree with suspended computations
--  data Search (A : Set) : Set where
--    fail : Search A
--    retn : A → Search A
--    fork : ∞ (Search A) → ∞ (Search A) → Search A

  data Search (A : Set) : Set where
    fail : Search A
    retn : A → Search A
    fork : ∞ (List (Search A)) → Search A

  {-# NO_TERMINATION_CHECK #-}
  mutual
    dfs : ∀ {m} → Rules → SearchTree m → Search (∃₂ (λ δ n → Subst (m + δ) n) × Rules)
    dfs rs₀ s = dfsAcc rs₀ s []

    dfsAcc : ∀ {m} → Rules → SearchTree m → Rules → Search (∃₂ (λ δ n → Subst (m + δ) n) × Rules)
    dfsAcc {_} rs₀ (done s) ap = retn (s , ap)
    dfsAcc {m} rs₀ (step f) ap = fork (~ (next <$> rs₀))
      where
        next : ∃ Rule → Search (∃₂ (λ δ n → Subst (m + δ) n) × Rules)
        next r = dfsAcc rs₀ (! f r) (ap ∷ʳ r)

  dfsToDepth : ∀ {A} → ℕ → Search A → List A
  dfsToDepth zero     _        = []
  dfsToDepth (suc k)  fail     = []
  dfsToDepth (suc k) (retn x)  = return x
  dfsToDepth (suc k) (fork xs) = concatMap (dfsToDepth k) (! xs)


  -- while we should be able to guarantee that the terms after substitution
  -- contain no variables (and all free variables in the domain occur because
  -- of unused rules), the required proof of this is currently still unimplemented
  -- therefore, we have to resort to using maybe

  mutual
    noVars : ∀ {n} → Term n → Maybe (Term 0)
    noVars (var x)    = nothing
    noVars (con s ts) = con s <$> noVarsChildren ts

    noVarsChildren : ∀ {n k} → Vec (Term n) k → Maybe (Vec (Term 0) k)
    noVarsChildren [] = just []
    noVarsChildren (t ∷ ts) = noVars t >>= λ t' →
                              noVarsChildren ts >>= λ ts' →
                              return (t' ∷ ts')

  -- `first` combinator from control.arrow
  first : {A B C : Set} → (A → B) → A × C → B × C
  first f (x , y) = f x , y

  filterWithVars' : ∀ {m} → List (∃ (λ n → Vec (Term n) m)) → List (Vec (Term 0) m)
  filterWithVars' = concatMap (fromMaybe ∘ noVarsChildren ∘ proj₂)

  filterWithVars : ∀ {m} → List (∃ (λ n → Vec (Term n) m) × Rules) → List (Vec (Term 0) m × Rules)
  filterWithVars {m} rs = concatMap (fromMaybe ∘ noVars') rs
    where
    noVars' : ∃ (λ n → Vec (Term n) m) × Rules → Maybe (Vec (Term 0) m × Rules)
    noVars' ((_ , x) , y) = noVarsChildren x >>= λ x → return (x , y)

  solveToDepth : ∀ {m} (depth : ℕ) → Rules → Goal m → List (∃ (λ n → Vec (Term n) m) × Rules)
  solveToDepth {m} depth rules goal = map (first envOf) $ subs
    where
    vars = allFin m
    tree = solve goal
    subs : List (∃ (λ δ → ∃ (Subst (m + δ))) × Rules)
    subs = dfsToDepth depth (dfs rules tree)
    envOf : ∃₂ (λ δ n → Subst (m + δ) n) → ∃ (λ n → Vec (Term n) m)
    envOf (δ , n , s) = _ , (vmap (λ v → apply s v) (vmap (injectL _) vars))


  -- Proof Terms
  --
  -- We can reconstruct the function/argument structure from the final proof
  -- tree, using the arity of the used rules and the fact that therefore the
  -- next `n` rule applications will go towards computing the arguments for the
  -- chosen rule.
  data Proof : Set where
    con : Name → List Proof → Proof

  -- |Reconstruct a list of rules as a proof tree. Anything but a list containing
  --  a single item can be considered an error (either there are multiple trees,
  --  or at some point there were not enough items to fill all a rule's arguments)
  toProofAcc : Rules → List Proof
  toProofAcc = foldr next []
    where
      next : ∃ Rule → List Proof → List Proof
      next r ps = next′
        where
          rₙ = name (proj₂ r)  -- name of the rule
          rₖ = arity (proj₂ r) -- number of subproofs needed by the rule
          pₖ = length ps       -- current number of proof terms

          next′ : List Proof
          next′ with compare rₖ pₖ
          next′ | tri< r<p r≢p r≯p = con rₙ (take rₖ ps) ∷ drop rₖ ps
          next′ | tri≈ r≮p r≡p r≯p = con rₙ ps ∷ []
          next′ | tri> r≮p r≢p r>p = [] -- this case should not occur

  -- |Reconstruct a list of rules as a proof tree. Runs `toProofAcc` above, and
  --  checks if the result is a list containing a single proof tree.
  toProof : Rules → Maybe Proof
  toProof rs with toProofAcc rs
  ... | []    = nothing
  ... | p ∷ _ = just p
