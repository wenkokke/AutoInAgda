open import Function using (_$_; _∘_; id; flip; const)
open import Category.Monad
open import Data.Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; compare; less; equal; greater) renaming (_⊔_ to max)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.String using (String)
open import Data.Sum as Sum using () renaming (_⊎_ to Either; inj₁ to left; inj₂ to right; [_,_] to fromEither)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Reflection renaming (_≟-Name_ to decEqName; _≟_ to decEqTerm)

module Auto where

  -- open up the classes we'll be using
  private
    open RawMonad {{...}}
    open DecSetoid {{...}} using (_≟_)
    MonadMaybe     = Maybe.monad
    MonadList      = List.monad
    ApplicativeVec = Vec.applicative
    NameDecSetoid  = PropEq.decSetoid decEqName
    NatDecSetoid   = PropEq.decSetoid Nat._≟_

  data Msg : Set where
    searchSpaceExhausted : Msg
    indexOutOfBounds     : Msg
    unsupportedSyntax    : Term → Msg
    panic!               : Msg

  data Err : Msg → Set where
    err : (msg : Msg) → Err msg

  Error : ∀ A → Set
  Error A = Either Msg A

  -- Agda Names & Prolog Names
  --
  -- We can extend Agda names to carry an arity and extend decidable equality to
  -- work with these Prolog names (PName).

  agdaTypeArity : Type → ℕ
  agdaTypeArity (el _ (pi _ t)) = suc (agdaTypeArity t)
  agdaTypeArity (el _ t)        = zero

  agdaNameArity : Name → ℕ
  agdaNameArity n = agdaTypeArity (type n)

  data PrologName : Set where
    pname : (n : Name) → PrologName
    pvar  : (i : ℕ) → PrologName
    pimpl : PrologName

  prologNameArity : PrologName → ℕ
  prologNameArity (pname n) = agdaNameArity n
  prologNameArity (pvar _)  = 0
  prologNameArity (pimpl)   = 2

  pname-injective : ∀ {x y} → pname x ≡ pname y → x ≡ y
  pname-injective refl = refl

  pvar-injective : ∀ {i j} → pvar i ≡ pvar j → i ≡ j
  pvar-injective refl = refl

  decEqPrologName : (x y : PrologName) → Dec (x ≡ y)
  decEqPrologName (pname x) (pname  y) with x ≟ y
  decEqPrologName (pname x) (pname .x) | yes refl = yes refl
  decEqPrologName (pname x) (pname  y) | no  x≢y  = no (x≢y ∘ pname-injective)
  decEqPrologName (pname _) (pvar _)   = no (λ ())
  decEqPrologName (pname _)  pimpl     = no (λ ())
  decEqPrologName (pvar _)  (pname _)  = no (λ ())
  decEqPrologName (pvar i)  (pvar  j)  with i ≟ j
  decEqPrologName (pvar i)  (pvar .i)  | yes refl = yes refl
  decEqPrologName (pvar i)  (pvar  j)  | no i≢j = no (i≢j ∘ pvar-injective)
  decEqPrologName (pvar _)   pimpl     = no (λ ())
  decEqPrologName  pimpl    (pname _)  = no (λ ())
  decEqPrologName  pimpl    (pvar _)   = no (λ ())
  decEqPrologName  pimpl     pimpl     = yes refl

  private
    PrologNameDecSetoid = PropEq.decSetoid decEqPrologName

  data RuleName : Set where
    rname : Name → RuleName
    rvar  : ℕ → RuleName

  -- Due to this functionality being unavailable and unimplementable in plain Agda
  -- we'll just have to postulate the existance of a show function for Agda names.
  -- Using this postulate we can then implement a show function for Prolog names.

  -- Now we can load the Prolog libraries.

  import Prolog
  module PI = Prolog RuleName PrologName decEqPrologName
  open PI public renaming (Term to PTerm)

  -- We'll implement a few basic functions to ease our working with Agda's
  -- Reflection library.

  unarg : ∀ {A} → Arg A → A
  unarg (arg _ _ x) = x

  unel : Type → Term
  unel (el _ t) = t

  -- We'll need the function below later on, when we try to convert found
  -- variables to finitely indexed variables within our domain `n`.

  convDef : (s : Name) → ∃ (λ n → List (PTerm n)) → ∃ PTerm
  convDef f (n , ts) = n , con (pname f) ts

  record Case : Set where
    field
      forVar : ℕ → ℕ → Error (∃  PTerm)
      forCon : (s : Name) → ∃ (λ n → List (PTerm n)) → ∃ PTerm
      forDef : (s : Name) → ∃ (λ n → List (PTerm n)) → ∃ PTerm

  CaseTerm : Case
  CaseTerm = record { forVar = convVar ; forCon = convDef ; forDef = convDef  }
    where
      convVar : ℕ → ℕ → Error (∃ PTerm)
      convVar  d i with compare d i
      convVar  d .(suc (d + k)) | less    .d k = left indexOutOfBounds
      convVar .i i              | equal   .i   = right (1     , var (Fin.fromℕ 0))
      convVar .(suc (i + k)) i  | greater .i k = right (suc k , var (Fin.fromℕ k))

  CaseGoal : Case
  CaseGoal = record { forVar = convPar ; forCon = convDef ; forDef = convDef }
    where
      convPar : ℕ → ℕ → Error (∃ PTerm)
      convPar  d i with compare d i
      convPar  d .(suc (d + k)) | less    .d k = left indexOutOfBounds
      convPar .i i              | equal   .i   = right (0 , con (pvar 0) [])
      convPar .(suc (i + k)) i  | greater .i k = right (0 , con (pvar k) [])

  splitTerm : ∀ {n} → PTerm n → List (PTerm n)
  splitTerm (con pimpl (t₁ ∷ t₂ ∷ [])) = t₁ ∷ splitTerm t₂
  splitTerm t = List.[ t ]

  mutual
    convAcc : Case → ℕ → Term → Error (∃ PTerm)
    convAcc dict d (var i [])   = Case.forVar dict d i
    convAcc dict d (var i args) = left (unsupportedSyntax (var i args))
    convAcc dict d (con c args) with convArgsAcc dict d args
    ... | left msg = left msg
    ... | right xs = right (Case.forCon dict c xs)
    convAcc dict d (def f args) with convArgsAcc dict d args
    ... | left msg = left msg
    ... | right xs = right (Case.forDef dict f xs)
    convAcc dict d (pi (arg visible _ (el _ t₁)) (el _ t₂))
      with convAcc dict d t₁ | convAcc dict (suc d) t₂
    ... | left msg | _        = left msg
    ... | _        | left msg = left msg
    ... | right (n₁ , p₁) | right (n₂ , p₂)
      with matchTerms p₁ p₂
    ... | (p₁′ , p₂′) = right (max n₁ n₂ , con pimpl (p₁′ ∷ p₂′ ∷ []))
    convAcc dict d (pi (arg _ _ _) (el _ t₂)) = convAcc dict (suc d) t₂
    convAcc dict d (lam v t) = left (unsupportedSyntax (lam v t))
    convAcc dict d (sort x)  = left (unsupportedSyntax (sort x))
    convAcc dict d unknown   = left (unsupportedSyntax (unknown))

    convArgsAcc : Case → ℕ → List (Arg Term) → Error (∃ (λ n → List (PTerm n)))
    convArgsAcc dict d [] = right (0 , [])
    convArgsAcc dict d (arg visible _ t ∷ ts) with convArgsAcc dict d ts
    convArgsAcc dict d (arg visible r t ∷ ts) | left msg = left msg
    convArgsAcc dict d (arg visible r t ∷ ts) | right _ with convAcc dict d t
    convArgsAcc dict d (arg visible r t ∷ ts) | right _ | left msg = left msg
    convArgsAcc dict d (arg visible r t ∷ ts) | right (n₂ , ps) | right (n₁ , p)
      with matchTermAndList p ps
    ... | (p′ , ps′) = right (max n₁ n₂ , p′ ∷ ps′)
    convArgsAcc dict d (arg _ _ _ ∷ ts) = convArgsAcc dict d ts

  convTerm : Term → Error (∃ PTerm)
  convTerm t = convAcc CaseTerm 0 t

  convGoal : Term → Error (∃ PTerm × Rules)
  convGoal t with convAcc CaseGoal 0 t
  ... | left msg = left msg
  ... | right (n , p) with reverse (splitTerm p)
  ... | []       = left panic!
  ... | (g ∷ rs) = right ((n , g) , mkArgs 0 rs)
    where
      mkArgs : ℕ → List (PTerm n) → Rules
      mkArgs i [] = []
      mkArgs i (t ∷ ts) = (n , rule (rvar i) t []) ∷ mkArgs (suc i) ts

  -- converts an agda term into a list of terms by splitting at each function
  -- symbol; note the order: the last element of the list will always be the
  -- conclusion of the funciton with the rest of the elements being the premises.

  -- convTerm′ : Term → Error (∃ (List ∘ PTerm))
  -- convTerm′ t with convTerm t
  -- convTerm′ t | left msg      = left msg
  -- convTerm′ t | right (n , p) = right (n , splitTerm p)

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
  mkRule : Name → Error (∃ Rule)
  mkRule name with convTerm (convName name)
  ... | left msg = left msg
  ... | right (n , t) = mkRule′ (n , splitTerm t)
    where
      mkRule′ : ∃ (List ∘ PTerm) → Error (∃ Rule)
      mkRule′ (n , xs) with initLast xs
      mkRule′ (n , .[]) | [] = left panic!
      mkRule′ (n , .(xs ++ x ∷ [])) | xs ∷ʳ' x = right (n , rule (rname name) x xs)

  mutual
    reify : Proof → Term
    reify (con (rvar i) ps) = var i []
    reify (con (rname n) ps) with definition n
    ... | function x   = def n (reifyChildren ps)
    ... | data-type x  = unknown
    ... | record′ x    = unknown
    ... | constructor′ = con n (reifyChildren ps)
    ... | axiom        = unknown
    ... | primitive′   = unknown

    reifyChildren : List Proof → List (Arg Term)
    reifyChildren [] = []
    reifyChildren (p ∷ ps) = toArg (reify p) ∷ reifyChildren ps
      where
        toArg : Term → Arg Term
        toArg = arg visible relevant

  quoteMsg : Msg → Term
  quoteMsg (searchSpaceExhausted) = quoteTerm (err searchSpaceExhausted)
  quoteMsg (indexOutOfBounds)     = quoteTerm (err indexOutOfBounds)
  quoteMsg (unsupportedSyntax x)  = quoteTerm (err (unsupportedSyntax x))
  quoteMsg (panic!)               = quoteTerm (err panic!)

  HintDB : Set
  HintDB = Rules

  hintdb : List Name → HintDB
  hintdb l = concatMap (fromError ∘ mkRule) l
    where
      fromError : {A : Set} → Error A → List A
      fromError = fromEither (const []) [_]

  ruleset : HintDB → Term → Maybe (∃ PTerm × Rules)
  ruleset rules type
    with convGoal type
  ... | left msg = nothing
  ... | right (g , args) = just (g , args ++ rules)

  auto : ℕ → HintDB → Term → Term
  auto depth rules type
    with convGoal type
  ... | left msg = quoteMsg msg
  ... | right ((n , g) , args)
    with solveToDepth depth (args ++ rules) g
  ... | [] = quoteMsg searchSpaceExhausted
  ... | (_ , ap) ∷ _
    with toProof ap
  ... | nothing = quoteMsg panic!
  ... | just p  = intros (reify p)
    where
      intros : Term → Term
      intros = introsAcc (length args)
        where
          introsAcc : ℕ → Term → Term
          introsAcc  zero   t = t
          introsAcc (suc k) t = lam visible (introsAcc k t)
