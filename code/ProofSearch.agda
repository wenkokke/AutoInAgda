open import Level using (_⊔_)
open import Function using (id; _∘_; _$_)
open import Coinduction using (∞; ♯_; ♭)
open import Data.Nat as Nat using (ℕ; suc; zero; _≤_; z≤n; s≤s; decTotalOrder)
open import Data.Nat.Properties as NatProps using (commutativeSemiring; distributiveLattice)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Fin.Props as FinProps renaming (_≟_ to _≟-Fin_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; monad)
open import Data.List as List using (List; _∷_; []; _++_; length; concat; map; foldr; concatMap; monad)
open import Data.List.Properties as ListProps renaming (∷-injective to ∷-inj)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Algebra as Alg using (CommutativeSemiring)
open import Category.Monad as Mon using (RawMonad)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary as Rel using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; trans; cong; cong₂)

module ProofSearch (RuleName : Set) (TermName : Set) (_≟-TermName_ : (x y : TermName) → Dec (x ≡ y)) where

  open Alg.CommutativeSemiring {{...}} using (_+_; +-comm; +-assoc)
  open Alg.DistributiveLattice {{...}} using (_∧_; ∧-comm)
  open Rel.DecTotalOrder {{...}} using (total)
  open Mon.RawMonad {{...}} using (return; _>>=_)
  open import Unification TermName _≟-TermName_ public hiding (_++_)

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b ⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B


  -- introduce rules
  record Rule (n : ℕ) : Set where
    constructor rule
    field
      name        : RuleName
      conclusion  : Term n
      premises    : List (Term n)

  open Rule using (name; conclusion; premises)

  -- compute the arity of a rule
  arity : ∀ {n} (r : Rule n) → ℕ
  arity = length ∘ premises

  -- compute difference from ≤
  diff : ∀ {m n} → m ≤ n → ∃[ k ] n ≡ m + k
  diff  z≤n    = _ , refl
  diff (s≤s p) = Prod.map id (cong suc) (diff p)


  -- type class for injections in the fashion of Fin.inject+
  record Inject (T : ℕ → Set) : Set where
    field
      inject : ∀ {m} n → T m → T (m + n)

    inject≤ : ∀ {m n} → m ≤ n → T m → T n
    inject≤ p t with diff p
    ... | k , n=m+k rewrite n=m+k = inject k t

  open Inject {{...}} using (inject; inject≤)


  -- type class for raising in the fashion of Fin.raise
  record Raise (T : ℕ → Set) : Set where
    field
      raise : ∀ {m} n → T m → T (n + m)

    raise≤ : ∀ {m n} → m ≤ n → T m → T n
    raise≤ {m} {n} p t with diff p
    ... | k , n=m+k rewrite n=m+k | +-comm m k = raise k t

  open Raise {{...}} using (raise; raise≤)


  -- instances for inject/raise for all used data types
  InjectFin   : Inject Fin
  InjectFin   = record { inject = Fin.inject+ }
  RaiseFin    : Raise  Fin
  RaiseFin    = record { raise  = Fin.raise }
  InjectTerm  : Inject Term
  InjectTerm  = record { inject = λ n → replace (var ∘ inject n) }
  RaiseTerm   : Raise  Term
  RaiseTerm   = record { raise  = λ m → replace (var ∘ raise m) }
  InjectTerms : Inject (List ∘ Term)
  InjectTerms = record { inject = λ n → List.map (inject n) }
  RaiseTerms  : Raise  (List ∘ Term)
  RaiseTerms  = record { raise  = λ m → List.map (raise m) }
  InjectGoals : ∀ {k} → Inject (λ n → Vec (Term n) k)
  InjectGoals = record { inject = λ n → Vec.map (inject n) }
  RaiseGoals  : ∀ {k} → Raise (λ n → Vec (Term n) k)
  RaiseGoals  = record { raise  = λ m → Vec.map (raise m) }
  InjectRule  : Inject Rule
  InjectRule  = record { inject = λ n → λ { (rule nm c p) → rule nm (inject n c) (inject n p) } }
  RaiseRule   : Raise Rule
  RaiseRule   = record { raise  = λ m → λ { (rule nm c p) → rule nm (raise m c) (raise m p) } }

  -- could rephrase inject/raise in terms of allowing modification by
  -- a function ℕ → ℕ, but really... why would I... it makes all the
  -- other instances much, much more obtuse
  injectSubst : ∀ {m n} (δ : ℕ) → Subst m n → Subst (m + δ) (n + δ)
  injectSubst _ nil = nil
  injectSubst δ (snoc s t x) = snoc (injectSubst δ s) (inject δ t) (inject δ x)


  private
    m≤n→m⊔n=n : ∀ {m n} → m ≤ n → m ∧ n ≡ n
    m≤n→m⊔n=n  z≤n    = refl
    m≤n→m⊔n=n (s≤s p) = cong suc (m≤n→m⊔n=n p)


  -- match indices of injectable data types
  match : ∀ {m n} {I J} {{i : Inject I}} {{j : Inject J}}
        → I m → J n → I (m ∧ n) × J (m ∧ n)
  match {m} {n} i j with total m n
  ... | inj₁ p rewrite              m≤n→m⊔n=n p = (inject≤ p i , j)
  ... | inj₂ p rewrite ∧-comm m n | m≤n→m⊔n=n p = (i , inject≤ p j)



  -- search trees
  data SearchTree (A : Set) : Set where
    fail : SearchTree A
    retn : A → SearchTree A
    fork : List (∞ (SearchTree A)) → SearchTree A

  -- lets try and keep the types readable, shall we?
  Goal   = Term
  Rules  = List (∃ Rule)

  data Proof : Set where
    con : (name : RuleName) (args : List Proof) → Proof

  -- representation of an incomplete proof
  Proof′ : ℕ → Set
  Proof′ m = ∃[ k ] Vec (Goal m) k × (Vec Proof k → Proof)

  con′ : ∀ {n k} (r : Rule n) → Vec Proof (arity r + k) → Vec Proof (suc k)
  con′ r xs = con (name r) (Vec.toList $ Vec.take (arity r) xs) ∷ Vec.drop (arity r) xs

  -- build search tree for a goal term
  {-# NO_TERMINATION_CHECK #-}
  solve : ∀ {m} → Goal m → Rules → SearchTree Proof
  solve {m} g rules = solveAcc {0} {m} (just (m , nil)) (1 , g ∷ [] , Vec.head)
    where
      solveAcc : ∀ {δ m} → Maybe (∃[ n ] Subst (δ + m) n) → Proof′ (δ + m) → SearchTree Proof
      solveAcc nothing _ = fail
      solveAcc (just (n , s)) (0 , [] , p) = retn (p [])
      solveAcc {δ} {m} (just (n , s)) (suc k , g ∷ gs , p) = fork (map step rules)
        where
          step : ∃[ δ′ ] Rule δ′ → ∞ (SearchTree Proof)
          step (δ′ , r) = ♯ solveAcc {δ′ + δ} {m} mgu prf
            where
              lem : δ′ + δ + m ≡ δ + m + δ′
              lem = trans (+-assoc δ′ δ m) (+-comm δ′ (δ + m))
              prf : Proof′ (δ′ + δ + m)
              prf = arity r + k , prm′ Vec.++ gs′ , p′
                where
                  gs′  : Vec (Goal (δ′ + δ + m)) k
                  gs′  rewrite lem = inject δ′ gs
                  prm′ : Vec (Goal (δ′ + δ + m)) (arity r)
                  prm′ rewrite lem = Vec.map (raise (δ + m)) (Vec.fromList (premises r))
                  p′   : Vec Proof (arity r + k) → Proof
                  p′   = p ∘ con′ r
              mgu : Maybe (∃[ n ] (Subst (δ′ + δ + m) n))
              mgu = unifyAcc g′ cnc′ s′
                where
                  g′   : Term (δ′ + δ + m)
                  g′   rewrite lem = inject δ′ g
                  cnc′ : Term (δ′ + δ + m)
                  cnc′ rewrite lem = raise (δ + m) (conclusion r)
                  s′   : ∃[ n ] Subst (δ′ + δ + m) n
                  s′   rewrite lem = n + δ′ , injectSubst δ′ s

  dfs : ∀ {A} (depth : ℕ) → SearchTree A → List A
  dfs  zero    _        = []
  dfs (suc k)  fail     = []
  dfs (suc k) (retn x)  = return x
  dfs (suc k) (fork xs) = concatMap (λ x → dfs k (♭ x)) xs

  bfs : ∀ {A} (depth : ℕ) → SearchTree A → List A
  bfs depth t = concat (Vec.toList (bfsAcc depth t))
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
      bfsAcc (suc k) (fork xs) = [] ∷ foldr merge empty (map (λ x → bfsAcc k (♭ x)) xs)
