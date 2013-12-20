open import Algebra
open import Algebra.Structures
open import Function using (id; const; flip; _∘_; _$_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Functor
open import Category.Monad
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; compare; less; equal; greater) renaming (_⊔_ to max)
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
    open StrictTotalOrder NatProps.strictTotalOrder renaming (compare to cmp)
    open CommutativeSemiring NatProps.commutativeSemiring using (+-assoc; +-identity)

  import Unification
  module UI = Unification Sym decEqSym
  open UI public using (Term; var; con)
  open UI using (Subst; snoc; nil; replace; apply; unifyAcc)

  data Rule (n : ℕ) : Set where
    rule : Name → Term n → List (Term n) → Rule n

  name : ∀ {n} → Rule n → Name
  name (rule name _ _) = name

  conclusion : ∀ {n} → Rule n → Term n
  conclusion (rule _ cnc _) = cnc

  premises : ∀ {n} → Rule n → List (Term n)
  premises (rule _ _ prm) = prm

  -- | compute the arity of a rule
  arity : ∀ {n} → Rule n → ℕ
  arity = length ∘ premises

  -- | alias for lists of rules
  Rules : Set
  Rules = List (∃ Rule)

  -- | alias for term to clarify its semantics
  Goal : ℕ → Set
  Goal n = Term n

  InjectL : (ℕ → Set) → Set
  InjectL I = ∀ {m} n → I m → I (m + n)
  InjectR : (ℕ → Set) → Set
  InjectR I = ∀ m {n} → I n → I (m + n)

  injFinL : InjectL Fin
  injFinL _  zero   = zero
  injFinL _ (suc i) = suc (injFinL _ i)

  injFinR : InjectR Fin
  injFinR zero   i = i
  injFinR (suc m) i = suc (injFinR m i)

  injTermL : InjectL Term
  injTermL n = replace (var ∘ injFinL n)

  injTermR : InjectR Term
  injTermR m = replace (var ∘ injFinR m)

  injListL : InjectL (List ∘ Term)
  injListL n = List.map (injTermL n)

  injListR : InjectR (List ∘ Term)
  injListR m = List.map (injTermR m)

  injVecL : ∀ {k} → InjectL (λ n → Vec (Term n) k)
  injVecL n = Vec.map (injTermL n)

  injVecR : ∀ {k} → InjectR (λ n → Vec (Term n) k)
  injVecR m = Vec.map (injTermR m)

  injRuleL : InjectL Rule
  injRuleL n (rule name cnc prm) = rule name (injTermL n cnc) (injListL n prm)

  injRuleR : InjectR Rule
  injRuleR m { n} (rule name cnc prm) = rule name (injTermR m cnc) (injListR m prm)

  -- TODO should be an instance of something like Indexed₂ or Indexed should be
  -- generalizeable to include the definiton for Subst; no hurry.
  injSubstL : ∀ {m n} (ε : ℕ) → Subst m n → Subst (m + ε) (n + ε)
  injSubstL _ nil = nil
  injSubstL ε (snoc s t x) = snoc (injSubstL ε s) (injTermL ε t) (injFinL ε x)

  -- some lemma's we'll need later on

  private
    max-lem₁ : (n k : ℕ) → max n (suc (n + k)) ≡ suc (n + k)
    max-lem₁ zero zero = refl
    max-lem₁ zero (suc k) = refl
    max-lem₁ (suc n) k = cong suc (max-lem₁ n k)

    max-lem₂ : (n : ℕ) → max n n ≡ n
    max-lem₂ zero = refl
    max-lem₂ (suc n) = cong suc (max-lem₂ n)

    max-lem₃ : (n k : ℕ) → max (suc (n + k)) n ≡ suc (n + k)
    max-lem₃ zero zero = refl
    max-lem₃ zero (suc k) = refl
    max-lem₃ (suc n) k = cong suc (max-lem₃ n k)

    m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
    m+1+n≡1+m+n zero    n = refl
    m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

  -- match takes two structures that are indexed internally by finite numbers
  -- and matches their domains (i.e. the new values will have their domains set
  -- to the largest of the previous domains).
  -- this is an rather generalized function, as it'll be needed for different
  -- combinations of fin-indexed datatypes. below you can find its three inst-
  -- antiations: matchTerms, matchTermAndList and matchTermAndVec.
  -- though all that is really needed is that that the structures (list and vec)
  -- have a decent implementation of rawfunctor, and then all this nonsense
  -- might be done away with.
  match : ∀ {n₁ n₂} {I₁ I₂} → InjectL I₁ → InjectL I₂
        → I₁ n₁ → I₂ n₂ → I₁ (max n₁ n₂) × I₂ (max n₁ n₂)
  match {n₁} {n₂} inj₁ inj₂ p₁ p₂ with compare n₁ n₂
  match {n₁} {.(suc (n₁ + k))} inj₁ inj₂ p₁ p₂ | less .n₁ k
    rewrite max-lem₁ n₁ k | sym (m+1+n≡1+m+n n₁ k) = (inj₁ (suc k) p₁ , p₂)
  match {n₁} {.n₁} inj₁ inj₂ p₁ p₂ | equal .n₁
    rewrite max-lem₂ n₁                            = (p₁ , p₂)
  match {.(suc (n₂ + k))} {n₂} inj₁ inj₂ p₁ p₂ | greater .n₂ k
    rewrite max-lem₃ n₂ k | sym (m+1+n≡1+m+n n₂ k) = (p₁ , inj₂ (suc k) p₂)

  matchTerms : ∀ {n₁ n₂} → Term n₁ → Term n₂ → Term (max n₁ n₂) × Term (max n₁ n₂)
  matchTerms {n₁} {n₂} = match {n₁} {n₂} {Term} {Term} injTermL injTermL

  matchTermAndList : ∀ {n₁ n₂} → Term n₁ → List (Term n₂) → Term (max n₁ n₂) × List (Term (max n₁ n₂))
  matchTermAndList {n₁} {n₂} = match {n₁} {n₂} {Term} {List ∘ Term} injTermL injListL

  matchTermAndVec : ∀ {k n₁ n₂} → Term n₁ → Vec (Term n₂) k → Term (max n₁ n₂) × Vec (Term (max n₁ n₂)) k
  matchTermAndVec {k} {n₁} {n₂} = match {n₁} {n₂} {Term} {λ n₂ → Vec (Term n₂) k} injTermL injVecL

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
        next (δ₂ , rule name cnc prm) = ~ solveAcc {m} {δ₁ + δ₂} mgu (prm' ++ gs')
          where
            lem : (m + (δ₁ + δ₂)) ≡ ((m + δ₁) + δ₂)
            lem = sym (+-assoc m δ₁ δ₂)

            -- compute an mgu for the current sub-goal and the chosen rule
            mgu : Maybe (∃ (λ n → Subst (m + (δ₁ + δ₂)) n))
            mgu = unifyAcc g' cnc' s'
              where

                -- lift arguments for unify into the new finite domain, making room for
                -- the variables used in the chosen rule.
                g'   : Term (m + (δ₁ + δ₂))
                g'   rewrite lem = injTermL δ₂ g
                s'   : ∃ (Subst (m + (δ₁ + δ₂)))
                s'   rewrite lem = n + δ₂ , injSubstL δ₂ s
                cnc' : Term (m + (δ₁ + δ₂))
                cnc' rewrite lem = injTermR (m + δ₁) cnc

            -- lift arguments for the recursive call to solve into the new finite domain,
            -- making room for the variables used in the chosen rule.
            gs'  : List (Term (m + (δ₁ + δ₂)))
            gs'  rewrite lem = injListL δ₂ gs
            prm' : List (Term (m + (δ₁ + δ₂)))
            prm' rewrite lem = injListR (m + δ₁) prm

  -- Concrete Search Tree
  --
  -- A concrete search tree is a realization of an abstract search tree, by explicit
  -- branching and rule applications. Aside from applying each rule, the transformation
  -- from abstract to concrete also maintains a list of each applied rule.

  data Search (A : Set) : Set where
    fail : Search A
    retn : A → Search A
    fork : ∞ (List (Search A)) → Search A

  Result : ℕ → Set
  Result m = ∃₂ (λ δ n → Subst (m + δ) n) × Rules

  mutual
    dfs : ∀ {m} → Rules → SearchTree m → Search (Result m)
    dfs rs₀ s = dfsAcc rs₀ s []

    dfsAcc : ∀ {m} → Rules → SearchTree m → Rules → Search (Result m)
    dfsAcc {_} rs₀ (done s) ap = retn (s , ap)
    dfsAcc {m} rs₀ (step f) ap = fork (~ (dfsAccChildren rs₀))
      where
        dfsAccChildren : Rules → List (Search (Result m))
        dfsAccChildren [] = []
        dfsAccChildren (r ∷ rs) = dfsAcc rs₀ (! f r) (ap ∷ʳ r) ∷ dfsAccChildren rs

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
  solveToDepth {m} depth rules goal = map (first mkEnv) $ subs
    where
    vars = allFin m
    tree = solve goal
    subs : List (∃ (λ δ → ∃ (Subst (m + δ))) × Rules)
    subs = dfsToDepth depth (dfs rules tree)
    mkEnv : ∃₂ (λ δ n → Subst (m + δ) n) → ∃ (λ n → Vec (Term n) m)
    mkEnv (δ , n , s) = _ , (Vec.map (λ v → apply s v) (Vec.map (injFinL _) vars))


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
          next′ with cmp rₖ pₖ
          next′ | tri< r<p r≢p r≯p = con rₙ (take rₖ ps) ∷ drop rₖ ps
          next′ | tri≈ r≮p r≡p r≯p = con rₙ ps ∷ []
          next′ | tri> r≮p r≢p r>p = [] -- this case should not occur

  -- |Reconstruct a list of rules as a proof tree. Runs `toProofAcc` above, and
  --  checks if the result is a list containing a single proof tree.
  toProof : Rules → Maybe Proof
  toProof rs with toProofAcc rs
  ... | []    = nothing
  ... | p ∷ _ = just p
