open import Algebra as Alg using ()
open import Function using (_∘_; _$_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Monad as Cat using ()
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; less; equal; greater) renaming (_⊔_ to max; compare to compare′)
open import Data.Nat.Properties as NatProps using ()
open import Data.Fin using (Fin; suc; zero)
open import Data.List as List hiding (monad)
open import Data.Vec as Vec using (Vec; []; _∷_; allFin; toList)
open import Data.Product as Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary as Rel using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)

module Prolog
  (RuleName : Set)
  (TermName : Set)
  (decEqTermName : (f g : TermName) → Dec (f ≡ g)) where

  private
    open Cat.RawMonad {{...}}
    open Rel.StrictTotalOrder NatProps.strictTotalOrder using (compare)
    open Alg.CommutativeSemiring NatProps.commutativeSemiring using (+-assoc; +-identity)
    MonadMaybe = Maybe.monad
    MonadList  = List.monad

  import Unification TermName decEqTermName as UI
  open UI public using (var; con) renaming (Term to PrologTerm)
  open UI using (Term; Subst; snoc; nil; replace; apply; unifyAcc)

  data Rule (n : ℕ) : Set where
    rule : RuleName → Term n → List (Term n) → Rule n

  ruleName : ∀ {n} → Rule n → RuleName
  ruleName (rule name _ _) = name

  conclusion : ∀ {n} → Rule n → Term n
  conclusion (rule _ cnc _) = cnc

  premises : ∀ {n} → Rule n → List (Term n)
  premises (rule _ _ prm) = prm

  -- compute the arity of a rule
  ruleArity : ∀ {n} → Rule n → ℕ
  ruleArity = length ∘ premises

  -- just an alias for a list of rules
  Rules : Set
  Rules = List (∃ Rule)

  -- just an alias for a term (but clearer! :)
  Goal : ℕ → Set
  Goal n = Term n

  InjectL : (ℕ → Set) → Set
  InjectL I = ∀ {m} n → I m → I (m + n)
  InjectR : (ℕ → Set) → Set
  InjectR I = ∀ m {n} → I n → I (m + n)

  injectFin : InjectL Fin
  injectFin _  zero   = zero
  injectFin _ (suc i) = suc (injectFin _ i)

  raiseFin : InjectR Fin
  raiseFin zero   i = i
  raiseFin (suc m) i = suc (raiseFin m i)

  injectTerm : InjectL Term
  injectTerm n = replace (var ∘ injectFin n)

  raiseTerm : InjectR Term
  raiseTerm m = replace (var ∘ raiseFin m)

  injectTermList : InjectL (List ∘ Term)
  injectTermList n = List.map (injectTerm n)

  raiseTermList : InjectR (List ∘ Term)
  raiseTermList m = List.map (raiseTerm m)

  -- injectTermVec : ∀ {k} → InjectL (λ n → Vec (Term n) k)
  -- injectTermVec n = Vec.map (injectTerm n)

  -- raiseTermVec : ∀ {k} → InjectR (λ n → Vec (Term n) k)
  -- raiseTermVec m = Vec.map (raiseTerm m)

  injectRule : InjectL Rule
  injectRule n (rule name cnc prm) = rule name (injectTerm n cnc) (injectTermList n prm)

  raiseRule : InjectR Rule
  raiseRule m { n} (rule name cnc prm) = rule name (raiseTerm m cnc) (raiseTermList m prm)

  -- TODO should be an instance of something like Indexed₂ or Indexed should be
  -- generalizeable to include the definiton for Subst; no hurry.
  injectSubst : ∀ {m n} (ε : ℕ) → Subst m n → Subst (m + ε) (n + ε)
  injectSubst _ nil = nil
  injectSubst ε (snoc s t x) = snoc (injectSubst ε s) (injectTerm ε t) (injectFin ε x)

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
  match {n₁} {n₂} inj₁ inj₂ p₁ p₂ with compare′ n₁ n₂
  match {n₁} {.(suc (n₁ + k))} inj₁ inj₂ p₁ p₂ | less .n₁ k
    rewrite max-lem₁ n₁ k | sym (m+1+n≡1+m+n n₁ k) = (inj₁ (suc k) p₁ , p₂)
  match {n₁} {.n₁} inj₁ inj₂ p₁ p₂ | equal .n₁
    rewrite max-lem₂ n₁                            = (p₁ , p₂)
  match {.(suc (n₂ + k))} {n₂} inj₁ inj₂ p₁ p₂ | greater .n₂ k
    rewrite max-lem₃ n₂ k | sym (m+1+n≡1+m+n n₂ k) = (p₁ , inj₂ (suc k) p₂)

  matchTerms : ∀ {n₁ n₂} → Term n₁ → Term n₂ → Term (max n₁ n₂) × Term (max n₁ n₂)
  matchTerms {n₁} {n₂} = match {n₁} {n₂} {Term} {Term} injectTerm injectTerm

  matchTermAndList : ∀ {n₁ n₂} → Term n₁ → List (Term n₂) → Term (max n₁ n₂) × List (Term (max n₁ n₂))
  matchTermAndList {n₁} {n₂} = match {n₁} {n₂} {Term} {List ∘ Term} injectTerm injectTermList

  -- matchTermAndVec : ∀ {k n₁ n₂} → Term n₁ → Vec (Term n₂) k → Term (max n₁ n₂) × Vec (Term (max n₁ n₂)) k
  -- matchTermAndVec {k} {n₁} {n₂} = match {n₁} {n₂} {Term} {λ n₂ → Vec (Term n₂) k} injectTerm injectTermVec

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
  --   n is always equal to 0. We can't---well, at least, I can't... so this
  --   is why we have the hack with the `filter noVars`

  data SearchSpace (m : ℕ) : Set where
    done : ∃₂ (λ δ n → Subst (m + δ) n) → SearchSpace m
    step : (∃ Rule → ∞ (SearchSpace m)) → SearchSpace m

  loop : ∀ {m} → SearchSpace m
  loop = step (λ _ → ~ loop)

  solve : ∀ {m} → Goal m → SearchSpace m
  solve {m} g = solveAcc {m} {0} (just (m , s₀)) (g₀ ∷ [])
    where

    -- small proofs that the initial domain (with room for m goal variables and
    -- 0 auxiliary variables) is equal to just the goal domain (with m variables)
    s₀ : Subst (m + 0) m
    s₀ rewrite proj₂ +-identity m = nil
    g₀ : Goal (m + 0)
    g₀ rewrite proj₂ +-identity m = g

    solveAcc : ∀ {m δ₁} → Maybe (∃ (λ n → Subst (m + δ₁) n)) → List (Goal (m + δ₁)) → SearchSpace m
    solveAcc {m} {δ₁} nothing _ = loop
    solveAcc {m} {δ₁} (just (n , s)) [] = done (δ₁ , n , s)
    solveAcc {m} {δ₁} (just (n , s)) (g ∷ gs) = step next
      where
        next : ∃ Rule → ∞ (SearchSpace m)
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
                g'   rewrite lem = injectTerm δ₂ g
                s'   : ∃ (Subst (m + (δ₁ + δ₂)))
                s'   rewrite lem = n + δ₂ , injectSubst δ₂ s
                cnc' : Term (m + (δ₁ + δ₂))
                cnc' rewrite lem = raiseTerm (m + δ₁) cnc

            -- lift arguments for the recursive call to solve into the new finite domain,
            -- making room for the variables used in the chosen rule.
            gs'  : List (Term (m + (δ₁ + δ₂)))
            gs'  rewrite lem = injectTermList δ₂ gs
            prm' : List (Term (m + (δ₁ + δ₂)))
            prm' rewrite lem = raiseTermList (m + δ₁) prm

  -- Concrete Search Tree
  --
  -- A concrete search tree is a realization of an abstract search tree, by explicit
  -- branching and rule applications. Aside from applying each rule, the transformation
  -- from abstract to concrete also maintains a list of each applied rule.

  data SearchTree (A : Set) : Set where
    fail : SearchTree A
    retn : A → SearchTree A
    fork : ∞ (List (SearchTree A)) → SearchTree A

  -- lets try and keep the types readable, shall we?
  Result : ℕ → Set
  Result m = ∃₂ (λ δ n → Subst (m + δ) n) × Rules

  mutual
    mkTree : ∀ {m} → Rules → SearchSpace m → SearchTree (Result m)
    mkTree rs₀ s = mkTreeAcc rs₀ s []

    mkTreeAcc : ∀ {m} → Rules → SearchSpace m → Rules → SearchTree (Result m)
    mkTreeAcc {_} rs₀ (done s) ap = retn (s , ap)
    mkTreeAcc {m} rs₀ (step f) ap = fork (~ (mkTreeAccChildren rs₀))
      where
        mkTreeAccChildren : Rules → List (SearchTree (Result m))
        mkTreeAccChildren [] = []
        mkTreeAccChildren (r ∷ rs) = mkTreeAcc rs₀ (! f r) (ap ∷ʳ r) ∷ mkTreeAccChildren rs

  dfs : ∀ {A} (depth : ℕ) → SearchTree A → List A
  dfs  zero    _        = []
  dfs (suc k)  fail     = []
  dfs (suc k) (retn x)  = return x
  dfs (suc k) (fork xs) = concatMap (dfs k) (! xs)

  bfs : ∀ {A} (depth : ℕ) → SearchTree A → List A
  bfs depth t = concat (toList (bfsAcc depth t))
    where
      merge : ∀ {A : Set} {k} → (xs ys : Vec (List A) k) → Vec (List A) k
      merge [] [] = []
      merge (x ∷ xs) (y ∷ ys) = (x ++ y) ∷ merge xs ys

      empty : ∀ {A : Set} {k} → Vec (List A) k
      empty {k = zero}  = []
      empty {k = suc k} = [] ∷ empty

      bfsAcc : ∀ {A} (depth : ℕ) → SearchTree A → Vec (List A) depth
      bfsAcc  zero   _         = []
      bfsAcc (suc k)  fail     = empty
      bfsAcc (suc k) (retn x)  = (x ∷ []) ∷ empty
      bfsAcc (suc k) (fork xs) = [] ∷ foldr merge empty (map (bfsAcc k) (! xs))

  -- while we should be able to guarantee that the terms after substitution
  -- contain no variables (and all free variables in the domain occur because
  -- of unused rules), the required proof of this is currently still unimplemented
  -- therefore, we have to resort to using maybe

  mutual
    noVars : ∀ {n} → Term n → Maybe (Term 0)
    noVars (var x)    = nothing
    noVars (con s ts) = con s <$> noVarsChildren ts

    noVarsChildren : ∀ {n} → List (Term n) → Maybe (List (Term 0))
    noVarsChildren [] = just []
    noVarsChildren (t ∷ ts) = noVars t >>= λ t' →
                              noVarsChildren ts >>= λ ts' →
                              return (t' ∷ ts')

  -- `first` combinator from control.arrow
  first : {A B C : Set} → (A → B) → A × C → B × C
  first f (x , y) = f x , y

  filterWithVars' : List (∃ (λ n → List (Term n))) → List (List (Term 0))
  filterWithVars' = concatMap (fromMaybe ∘ noVarsChildren ∘ proj₂)

  filterWithVars : List (∃ (λ n → List (Term n)) × Rules) → List (List (Term 0) × Rules)
  filterWithVars rs = concatMap (fromMaybe ∘ noVars′) rs
    where
      noVars′ : ∃ (λ n → List (Term n)) × Rules → Maybe (List (Term 0) × Rules)
      noVars′ ((_ , x) , y) = noVarsChildren x >>= λ x → return (x , y)

  solveToDepth : ∀ {m} (depth : ℕ) → Rules → Goal m → List (∃ (λ n → Vec (Term n) m) × Rules)
  solveToDepth {m} depth rules goal = map (first mkEnv) $ subs
    where
      vars = allFin m
      tree = mkTree rules (solve goal)
      subs : List (∃ (λ δ → ∃ (Subst (m + δ))) × Rules)
      subs = dfs depth tree
      mkEnv : ∃₂ (λ δ n → Subst (m + δ) n) → ∃ (λ n → Vec (Term n) m)
      mkEnv (δ , n , s) = _ , (Vec.map (λ v → apply s v) (Vec.map (injectFin _) vars))


  -- Proof Terms
  --
  -- We can reconstruct the function/argument structure from the final proof
  -- tree, using the arity of the used rules and the fact that therefore the
  -- next `n` rule applications will go towards computing the arguments for the
  -- chosen rule.
  data Proof : Set where
    con : RuleName → List Proof → Proof

  -- |Reconstruct a list of rules as a proof tree. Anything but a list containing
  --  a single item can be considered an error (either there are multiple trees,
  --  or at some point there were not enough items to fill all a rule's arguments)
  toProofAcc : Rules → List Proof
  toProofAcc = foldr next []
    where
      next : ∃ Rule → List Proof → List Proof
      next r ps = next′
        where
          name      = ruleName (proj₂ r)      -- name of the rule
          arity     = ruleArity (proj₂ r) -- number of subproofs needed by the rule
          numProofs = length ps           -- current number of proof terms

          next′ : List Proof
          next′ with compare arity numProofs
          next′ | tri< r<p r≢p r≯p = con name (take arity ps) ∷ drop arity ps
          next′ | tri≈ r≮p r≡p r≯p = con name ps ∷ []
          next′ | tri> r≮p r≢p r>p = [] -- this case should not occur

  -- |Reconstruct a list of rules as a proof tree. Runs `toProofAcc` above, and
  --  checks if the result is a list containing a single proof tree.
  toProof : Rules → Maybe Proof
  toProof rs with toProofAcc rs
  ... | []    = nothing
  ... | p ∷ _ = just p
