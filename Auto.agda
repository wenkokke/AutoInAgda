open import Function using (_$_; _∘_; id; flip)
open import Category.Monad
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; compare; less; equal; greater) renaming (_⊔_ to max)
open import Data.List as List
  using (List; []; _∷_; [_]; map; _++_; foldr; concatMap; length; InitLast; reverse; initLast; _∷ʳ'_; fromMaybe)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Reflection

module Auto where

  -- open up the classes we'll be using
  private
    open RawMonad {{...}}
    MonadMaybe     = Maybe.monad
    MonadList      = List.monad
    ApplicativeVec = Vec.applicative

  -- Agda Names & Prolog Names
  --
  -- We can extend Agda names to carry an arity and extend decidable equality to
  -- work with these Prolog names (PName).

  data PName : ℕ → Set where
    pname : (n : Name) (k : ℕ) → PName k
    pimpl : PName 2

  _≟-PName_ : ∀ {k} (x y : PName k) → Dec (x ≡ y)
  _≟-PName_ pimpl pimpl = yes refl
  _≟-PName_ (pname x .2) pimpl = no (λ ())
  _≟-PName_ pimpl (pname y .2) = no (λ ())
  _≟-PName_ {k} (pname x .k) (pname  y .k) with x ≟-Name y
  _≟-PName_ {k} (pname x .k) (pname .x .k) | yes refl = yes refl
  _≟-PName_ {k} (pname x .k) (pname  y .k) | no  x≢y  = no (x≢y ∘ elim)
    where
      elim : ∀ {k x y} → pname x k ≡ pname y k → x ≡ y
      elim {_} {x} {.x} refl = refl

  -- Due to this functionality being unavailable and unimplementable in plain Agda
  -- we'll just have to postulate the existance of a show function for Agda names.
  -- Using this postulate we can then implement a show function for Prolog names.

  postulate
    primShowQName : Name → String

  showPName : ∀ {n} → PName n → String
  showPName (pname n _) = primShowQName n
  showPName (impl) = "→"

  -- Now we can load the Prolog and Prolog.Show libraries.

  import Prolog
  module PI = Prolog Name PName _≟-PName_
  open PI public
    using (Rules; Rule; rule; conclusion; premises; Proof; var; con
          ; solveToDepth; toProof)
    renaming (Term to PTerm; injectTermL to injTerm)

  import Prolog.Show
  module PSI = Prolog.Show Name primShowQName PName showPName _≟-PName_

  -- We'll implement a few basic functions to ease our working with Agda's
  -- Reflection library.

  unarg : ∀ {A} → Arg A → A
  unarg (arg _ _ x) = x

  unel : Type → Term
  unel (el _ t) = t

  -- We'll need the function below later on, when we try to convert found
  -- variables to finitely indexed variables within our domain `n`.

  toFin : (m n : ℕ) → Maybe (Fin m)
  toFin  zero    zero   = nothing
  toFin  zero   (suc n) = nothing
  toFin (suc m)  zero   = just zero
  toFin (suc m) (suc n) = suc <$> toFin m n

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
  match : {n₁ n₂ : ℕ}
          {T₁ T₂ : ℕ → Set}                  -- ^ two type constructors and
          (inj₁ : ∀ k → T₁ n₁ → T₁ (n₁ + k)) -- ^ injection functions for both
          (inj₂ : ∀ k → T₂ n₂ → T₂ (n₂ + k)) -- ^ type constructors
          → T₁ n₁ → T₂ n₂ → T₁ (max n₁ n₂) × T₂ (max n₁ n₂)
  match {n₁} {n₂} inj₁ inj₂ p₁ p₂ with compare n₁ n₂
  match {n₁} {.(suc (n₁ + k))} inj₁ inj₂ p₁ p₂ | less .n₁ k
    rewrite max-lem₁ n₁ k | sym (m+1+n≡1+m+n n₁ k)
    = (inj₁ (suc k) p₁ , p₂)
  match {n₁} {.n₁} inj₁ inj₂ p₁ p₂ | equal .n₁
    rewrite max-lem₂ n₁
    = (p₁ , p₂)
  match {.(suc (n₂ + k))} {n₂} inj₁ inj₂ p₁ p₂ | greater .n₂ k
    rewrite max-lem₃ n₂ k | sym (m+1+n≡1+m+n n₂ k)
    = (p₁ , inj₂ (suc k) p₂)

  matchTerms : ∀ {n₁ n₂} → PTerm n₁ → PTerm n₂ → PTerm (max n₁ n₂) × PTerm (max n₁ n₂)
  matchTerms {n₁} {n₂} = match {n₁} {n₂} {PTerm} {PTerm} injTerm injTerm

  matchTermAndList : ∀ {n₁ n₂} → PTerm n₁ → List (PTerm n₂) → PTerm (max n₁ n₂) × List (PTerm (max n₁ n₂))
  matchTermAndList {n₁} {n₂} = match {n₁} {n₂} {PTerm} {List ∘ PTerm} injTerm injList
    where
      injList : ∀ {m} n → List (PTerm m) → List (PTerm (m + n))
      injList n l = injTerm n <$> l

  matchTermAndVec : ∀ {k n₁ n₂} → PTerm n₁ → Vec (PTerm n₂) k → PTerm (max n₁ n₂) × Vec (PTerm (max n₁ n₂)) k
  matchTermAndVec {k} {n₁} {n₂} = match {n₁} {n₂} {PTerm} {λ n₂ → Vec (PTerm n₂) k} injTerm injVec
    where
      injVec : ∀ {k m} n → Vec (PTerm m) k → Vec (PTerm (m + n)) k
      injVec n v = Vec.map (injTerm n) v

  convDef : Name → ∃₂ (λ k n → Vec (PTerm n) k) → ∃ PTerm
  convDef f (k , n , ts) = n , con (pname f k) ts

  mutual
    convTermAcc : ℕ → ℕ → Term → Maybe (∃ PTerm)
    convTermAcc δ d (var x args)               = nothing
    convTermAcc δ d (con c args)               = nothing
    convTermAcc δ d (def f args)
      with convArgsAcc δ d args
    ... | just xs     = just (convDef f xs)
    ... | nothing     = nothing
    convTermAcc δ d (pi (arg visible r (el _ t₁)) (el _ t₂))
      with convTermAcc δ d t₁ | convTermAcc δ (suc d) t₂
    ... | _              | nothing             = nothing
    ... | nothing        | _                   = nothing
    ... | just (n₁ , p₁) | just (n₂ , p₂)
      with matchTerms p₁ p₂
    ... | (p₁′ , p₂′) = just (max n₁ n₂ , con pimpl (p₁′ ∷ p₂′ ∷ []))
    convTermAcc δ d (pi (arg _ _ _) (el _ t₂)) = convTermAcc (suc δ) d t₂
    convTermAcc δ d (lam v t)                  = nothing
    convTermAcc δ d (sort x)                   = nothing
    convTermAcc δ d unknown                    = nothing

    convArgsAcc : ℕ → ℕ → List (Arg Term) → Maybe (∃₂ (λ k n → Vec (PTerm n) k))
    convArgsAcc δ d [] = just (0 , 0 , [])
    convArgsAcc δ d (arg visible _ t ∷ ts) with convArgsAcc δ d ts
    convArgsAcc δ d (arg visible r t ∷ ts) | just ps with convTermAcc δ d t
    convArgsAcc δ d (arg visible r t ∷ ts) | just (k , n₂ , ps) | just (n₁ , p)
      with matchTermAndVec p ps
    ... | (p′ , ps′) = just (suc k , max n₁ n₂ , p′ ∷ ps′)
    convArgsAcc δ d (arg visible r t ∷ ts) | just ps | nothing = nothing
    convArgsAcc δ d (arg visible r t ∷ ts) | nothing = nothing
    convArgsAcc δ d (arg _       _ _ ∷ ts) = convArgsAcc δ d ts

  convTerm : Term → Maybe (∃ PTerm)
  convTerm = convTermAcc 0 0

  -- converts an agda term into a list of terms by splitting at each function
  -- symbol; note the order: the last element of the list will always be the
  -- conclusion of the funciton with the rest of the elements being the premises.
  convTerm′ : Term → Maybe (∃ (List ∘ PTerm))
  convTerm′ (pi (arg visible _ (el _ t₁)) (el _ t₂))
    with convTerm t₁ | convTerm′ t₂
  ... | nothing       | _              = nothing
  ... | _             | nothing        = nothing
  ... | just (n₁ , p) | just (n₂ , ps)
    with matchTermAndList p ps
  ... | p′ , ps′ = just (max n₁ n₂ , p′ ∷ ps′)
  convTerm′ t
    with convTerm t
  convTerm′ t | just (n , p) = just (n , [ p ])
  convTerm′ t | nothing      = nothing

  -- We're interested in the rules formed by our types, so we will create a
  -- term by checking the type associated with a name and then removing the
  -- type constructor `el`.
  convName : Name → Term
  convName = unel ∘ type

  -- name2rule:
  --   converts names into a single rule, where the function type for the name
  --   is split at every top-level fuction symbol; for instance, for function
  --   composition (of type (B → C) → (A → B) → A → C) we will get the following
  --   rule:
  --
  --     C :- A, A → B, B → C.
  --
  --   for this conversion strategy to work, we must ensure that when we start the
  --   proof search for a type with top-level function symbols we first introduce
  --   all hypotheses by lambda abstraction (as would have been done by the intros
  --   tactic). furthermore, for usage with higher-order function types we would
  --   still need to add an inference rule for function application in order to
  --   be able to apply them (as with name2rule″).
  mkRule : Name → Maybe (∃ Rule)
  mkRule name = mkRule′ =<< convTerm′ (convName name)
    where
      mkRule′ : ∃ (List ∘ PTerm) → Maybe (∃ Rule)
      mkRule′ (n , xs) with initLast xs
      mkRule′ (n , .[]) | [] = nothing
      mkRule′ (n , .(xs ++ x ∷ [])) | xs ∷ʳ' x = just (n , rule name x xs)

  mutual
    reify : Proof → Term
    reify (con n ps) = def n (reifyChildren ps)

    reifyChildren : List Proof → List (Arg Term)
    reifyChildren [] = []
    reifyChildren (p ∷ ps) = toArg (reify p) ∷ reifyChildren ps
      where
        toArg : Term → Arg Term
        toArg = arg visible relevant

  -- TODO add error messages to conversion functions and reify into an error datatype
  -- whenever an error occurs, plus generate an error message when the search space is
  -- exhausted
  reifyError : Maybe Proof → Term
  reifyError nothing = unknown
  reifyError (just p) = reify p


  auto : ℕ → List Name → Term → Term
  auto depth names type = result
    where
      goal : Maybe (∃ PTerm)
      goal = convTerm type

      rules : Rules
      rules = concatMap (fromMaybe ∘ mkRule) names

      result : Term
      result with goal
      result | nothing = unknown
      result | just (n , g) with (solveToDepth depth rules g)
      result | just (_ , _) | [] = unknown
      result | just (_ , _) | (_ , ap) ∷ _ with (toProof ap)
      result | just (_ , _) | (_ , ap) ∷ _ | nothing = unknown
      result | just (_ , _) | (_ , ap) ∷ _ | just p  = reify p
