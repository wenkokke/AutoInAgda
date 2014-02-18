open import Algebra as Alg using ()
open import Function using (_∘_; _$_)
open import Coinduction using (∞) renaming (♯_ to ~_; ♭ to !_)
open import Category.Monad as Cat using ()
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _≤?_; compare; less; equal; greater) renaming (_⊔_ to max)
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
    open Alg.CommutativeSemiring NatProps.commutativeSemiring using (+-assoc; +-identity)
    MonadMaybe = Maybe.monad
    MonadList  = List.monad

  import Unification TermName decEqTermName as UI
  open UI public using (var; con) renaming (Term to PrologTerm)
  open UI using (Term; Subst; snoc; nil; replace; apply; unifyAcc)

  data Rule (n : ℕ) : Set where
    rule : RuleName → Term n → List (Term n) → Rule n

  name : ∀ {n} → Rule n → RuleName
  name (rule nm _ _) = nm

  conclusion : ∀ {n} → Rule n → Term n
  conclusion (rule _ cnc _) = cnc

  premises : ∀ {n} → Rule n → List (Term n)
  premises (rule _ _ prm) = prm

  -- compute the arity of a rule
  arity : ∀ {n} → Rule n → ℕ
  arity = length ∘ premises

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
    m⊔1+m+k=1+m+k : (n k : ℕ) → max n (suc (n + k)) ≡ suc (n + k)
    m⊔1+m+k=1+m+k zero zero = refl
    m⊔1+m+k=1+m+k zero (suc k) = refl
    m⊔1+m+k=1+m+k (suc n) k = cong suc (m⊔1+m+k=1+m+k n k)

    m⊔m=m : (n : ℕ) → max n n ≡ n
    m⊔m=m zero = refl
    m⊔m=m (suc n) = cong suc (m⊔m=m n)

    1+m+k⊔m=1+m+k : (n k : ℕ) → max (suc (n + k)) n ≡ suc (n + k)
    1+m+k⊔m=1+m+k zero zero = refl
    1+m+k⊔m=1+m+k zero (suc k) = refl
    1+m+k⊔m=1+m+k (suc n) k = cong suc (1+m+k⊔m=1+m+k n k)

    1+m+n=m+1+n : ∀ m n → suc (m + n) ≡ m + suc n
    1+m+n=m+1+n zero     n = refl
    1+m+n=m+1+n (suc m)  n = cong suc (1+m+n=m+1+n m n)

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
    rewrite m⊔1+m+k=1+m+k n₁ k | 1+m+n=m+1+n n₁ k = (inj₁ (suc k) p₁ , p₂)
  match {n₁} {.n₁} inj₁ inj₂ p₁ p₂             | equal .n₁
    rewrite m⊔m=m n₁                            = (p₁ , p₂)
  match {.(suc (n₂ + k))} {n₂} inj₁ inj₂ p₁ p₂ | greater .n₂ k
    rewrite 1+m+k⊔m=1+m+k n₂ k | 1+m+n=m+1+n n₂ k = (p₁ , inj₂ (suc k) p₂)

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
    fail : SearchSpace m
    retn : ∀ {δ n} → Subst (m + δ) n → SearchSpace m
    step : (∃ Rule → ∞ (SearchSpace m)) → SearchSpace m

  loop : ∀ {m} → SearchSpace m
  loop = step (λ _ → ~ loop)

  resolve : ∀ {m} → Goal m → SearchSpace m
  resolve {m} g = resolveAcc {m} {0} (just (m , s₀)) (g₀ ∷ [])
    where

    -- small proofs that the initial domain (with room for m goal variables and
    -- 0 auxiliary variables) is equal to just the goal domain (with m variables)
    s₀ : Subst (m + 0) m
    s₀ rewrite proj₂ +-identity m = nil
    g₀ : Goal (m + 0)
    g₀ rewrite proj₂ +-identity m = g

    resolveAcc : ∀ {m δ} → Maybe (∃ (λ n → Subst (m + δ) n)) → List (Goal (m + δ)) → SearchSpace m
    resolveAcc {m} {δ} nothing _ = fail
    resolveAcc {m} {δ} (just (n , s)) [] = retn s
    resolveAcc {m} {δ} (just (n , s)) (g ∷ gs) = step next
      where
        next : ∃ Rule → ∞ (SearchSpace m)
        next (δ₂ , r) = ~ resolveAcc mgu (prm' ++ gs')
          where
            lem : (m + (δ + δ₂)) ≡ ((m + δ) + δ₂)
            lem = sym (+-assoc m δ δ₂)

            -- compute an mgu for the current sub-goal and the chosen rule
            mgu : Maybe (∃ (λ n → Subst (m + (δ + δ₂)) n))
            mgu = unifyAcc g' cnc' s'
              where
                -- lift arguments for unify into the new finite domain, making room for
                -- the variables used in the chosen rule.
                g'   : Term (m + (δ + δ₂))
                g'   rewrite lem = injectTerm δ₂ g
                s'   : ∃ (Subst (m + (δ + δ₂)))
                s'   rewrite lem = n + δ₂ , injectSubst δ₂ s
                cnc' : Term (m + (δ + δ₂))
                cnc' rewrite lem = raiseTerm (m + δ) (conclusion r)

            -- lift arguments for the recursive call to resolve into the new finite domain,
            -- making room for the variables used in the chosen rule.
            gs'  : List (Term (m + (δ + δ₂)))
            gs'  rewrite lem = injectTermList δ₂ gs
            prm' : List (Term (m + (δ + δ₂)))
            prm' rewrite lem = raiseTermList (m + δ) (premises r)

  -- Concrete Search Tree
  --
  -- A concrete search tree is a realization of an abstract search tree, by explicit
  -- branching and rule applications. Aside from applying each rule, the transformation
  -- from abstract to concrete also maintains a list of each applied rule.

  data SearchTree (A : Set) : Set where
    fail : SearchTree A
    retn : A → SearchTree A
    fork : List (∞ (SearchTree A)) → SearchTree A

  -- lets try and keep the types readable, shall we?
  Result : ℕ → Set
  Result m = ∃₂ (λ δ n → Subst (m + δ) n) × Rules

  mutual

  -- Here's the version used in the paper
  -- mkTree : ∀ {m} -> Rules → SearchSpace m → SearchTree (Result m)
  -- mkTree rs₀ s = mkTreeAcc s []
  --   where
  --   mkTreeAcc : ∀ {m} -> SearchSpace m → Rules → SearchTree (Result m)
  --   mkTreeAcc fail _ = fail
  --   mkTreeAcc (retn s) acc = retn ((_ , (_ , s)) , acc)
  --   mkTreeAcc (step f) acc = 
  --     fork (map (\r -> ~ mkTreeAcc (! f r) (acc ∷ʳ r)) rs₀)

    mkTree : ∀ {m} → Rules → SearchSpace m → SearchTree (Result m)
    mkTree rs₀ s = mkTreeAcc rs₀ s []

    mkTreeAcc : ∀ {m} → Rules → SearchSpace m → Rules → SearchTree (Result m)
    mkTreeAcc {_} rs₀ fail _ = fail
    mkTreeAcc {_} rs₀ (retn s) ap = retn ((_ , (_ , s)) , ap)
    mkTreeAcc {m} rs₀ (step f) ap = fork (mkTreeAccChildren rs₀)
      where
        -- when written with a simple `map`, termination checker complains
        mkTreeAccChildren : Rules → List (∞ (SearchTree (Result m)))
        mkTreeAccChildren [] = []
        mkTreeAccChildren (r ∷ rs) = 
          ~ (mkTreeAcc rs₀ (! f r) (ap ∷ʳ r)) ∷ mkTreeAccChildren rs 

  dfs : ∀ {A} (depth : ℕ) → SearchTree A → List A
  dfs  zero    _        = []
  dfs (suc k)  fail     = []
  dfs (suc k) (retn x)  = return x
  dfs (suc k) (fork xs) = concatMap (\x -> dfs k (! x)) xs

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
      bfsAcc (suc k) (fork xs) = [] ∷ foldr merge empty (map (\x -> bfsAcc k (! x)) xs)

  searchToDepth : ∀ {m} (depth : ℕ) → Rules → Goal m → List (Result m)
  searchToDepth {m} depth rules goal = dfs depth (mkTree rules (resolve goal))

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

  filterWithVars : List (∃ (λ n → List (Term n)) × Rules) → List (List (Term 0) × Rules)
  filterWithVars rs = concatMap (fromMaybe ∘ noVars′) rs
    where
      noVars′ : ∃ (λ n → List (Term n)) × Rules → Maybe (List (Term 0) × Rules)
      noVars′ ((_ , x) , y) = noVarsChildren x >>= λ x → return (x , y)

  -- Proof Terms
  --
  -- We can reconstruct the function/argument structure from the final proof
  -- tree, using the arity of the used rules and the fact that therefore the
  -- next `n` rule applications will go towards computing the arguments for the
  -- chosen rule.
  data ProofTerm : Set where
    con : RuleName → List ProofTerm → ProofTerm

  -- |Reconstruct a list of rules as a proof tree. Anything but a list containing
  --  a single item can be considered an error (either there are multiple trees,
  --  or at some point there were not enough items to fill all a rule's arguments)
  toProofTerms : Rules → List ProofTerm
  toProofTerms = foldr next []
    where
      next : ∃ Rule → List ProofTerm → List ProofTerm
      next (δ , r) pfs with arity r ≤? length pfs
      ... | yes r≤p = con (name r) (take (arity r) pfs) ∷ (drop (arity r) pfs)
      ... | no  r>p = []

  -- |Reconstruct a list of rules as a proof tree. Runs `toProofTerms` above, and
  --  checks if the result is a list containing a single proof tree.
  toProofTerm : Rules → Maybe ProofTerm
  toProofTerm rs with toProofTerms rs
  ... | []    = nothing
  ... | p ∷ _ = just p
