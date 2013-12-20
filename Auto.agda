open import Function using (_$_; _∘_; id; flip; const)
open import Category.Monad
open import Data.Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _≟_; compare; less; equal; greater) renaming (_⊔_ to max)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List
  using (List; []; _∷_; [_]; map; _++_; foldr; concatMap; length; InitLast; reverse; initLast; _∷ʳ'_; fromMaybe)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.String using (String)
open import Data.Sum renaming (_⊎_ to Either; inj₁ to left; inj₂ to right; [_,_] to fromEither)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Reflection
  using (Name; _≟-Name_
        ; type; Type; el
        ; Term; def; var; con; lam; pi; sort; unknown
        ; Arg; arg; visible; relevant
        ; definition; Definition; function; data-type; record′; constructor′; axiom; primitive′)

module Auto where

  -- open up the classes we'll be using
  private
    open RawMonad {{...}}
    MonadMaybe     = Maybe.monad
    MonadList      = List.monad
    ApplicativeVec = Vec.applicative

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

  data PName : ℕ → Set where
    pname : (n : Name) (k : ℕ) → PName k
    pvar  : (i : ℕ) → PName 0
    pimpl : PName 2

  data RName : Set where
    rdef : Name → RName
    rvar  : ℕ → RName

  _≟-PName_ : ∀ {k} (x y : PName k) → Dec (x ≡ y)
  _≟-PName_ {.2}  pimpl       pimpl       = yes refl
  _≟-PName_ {.2} (pname x .2) pimpl       = no (λ ())
  _≟-PName_ {.2}  pimpl      (pname y .2) = no (λ ())
  _≟-PName_ {.0} (pname x .0)(pvar i)     = no (λ ())
  _≟-PName_ {.0} (pvar i)    (pname y .0) = no (λ ())
  _≟-PName_ {k} (pname x .k) (pname  y .k) with x ≟-Name y
  _≟-PName_ {k} (pname x .k) (pname .x .k) | yes refl = yes refl
  _≟-PName_ {k} (pname x .k) (pname  y .k) | no  x≢y  = no (x≢y ∘ elim)
    where
      elim : ∀ {k x y} → pname x k ≡ pname y k → x ≡ y
      elim {_} {x} {.x} refl = refl
  _≟-PName_ {.0} (pvar i) (pvar  j) with i ≟ j
  _≟-PName_ {.0} (pvar i) (pvar .i) | yes refl = yes refl
  _≟-PName_ {.0} (pvar i) (pvar  j) | no  i≢j  = no (i≢j ∘ elim)
    where
      elim : ∀ {i j} → pvar i ≡ pvar j → i ≡ j
      elim {i} {.i} refl = refl

  -- Due to this functionality being unavailable and unimplementable in plain Agda
  -- we'll just have to postulate the existance of a show function for Agda names.
  -- Using this postulate we can then implement a show function for Prolog names.

  postulate
    primShowQName : Name → String

  showPName : ∀ {n} → PName n → String
  showPName (pname n _) = primShowQName n
  showPName (pvar i)    = showℕ i
  showPName (pimpl)     = "→"

  -- Now we can load the Prolog and Prolog.Show libraries.

  import Prolog
  module PI = Prolog RName PName _≟-PName_
  open PI public renaming (Term to PTerm)

  -- We'll implement a few basic functions to ease our working with Agda's
  -- Reflection library.

  unarg : ∀ {A} → Arg A → A
  unarg (arg _ _ x) = x

  unel : Type → Term
  unel (el _ t) = t

  -- We'll need the function below later on, when we try to convert found
  -- variables to finitely indexed variables within our domain `n`.

  convDef : Name → ∃₂ (λ k n → Vec (PTerm n) k) → ∃ PTerm
  convDef f (k , n , ts) = n , con (pname f k) ts

  convVar : ℕ → ℕ → Error (∃ PTerm)
  convVar  d i with compare d i
  convVar  d .(suc (d + k)) | less    .d k = left indexOutOfBounds
  convVar .i i              | equal   .i   = right (1     , var (Fin.fromℕ 0))
  convVar .(suc (i + k)) i  | greater .i k = right (suc k , var (Fin.fromℕ k))

  mutual
    convTermAcc : ℕ → Term → Error (∃ PTerm)
    convTermAcc d (var i [])   = convVar d i
    convTermAcc d (var i args) = left (unsupportedSyntax (var i args))
    convTermAcc d (con c args)
      with convArgsAcc d args
    ... | right xs = right (convDef c xs)
    ... | left msg = left msg
    convTermAcc d (def f args)
      with convArgsAcc d args
    ... | right xs = right (convDef f xs)
    ... | left msg = left msg
    convTermAcc d (pi (arg visible r (el _ t₁)) (el _ t₂))
      with convTermAcc d t₁ | convTermAcc (suc d) t₂
    ... | left msg | _        = left msg
    ... | _        | left msg = left msg
    ... | right (n₁ , p₁) | right (n₂ , p₂)
      with matchTerms p₁ p₂
    ... | (p₁′ , p₂′) = right (max n₁ n₂ , con pimpl (p₁′ ∷ p₂′ ∷ []))
    convTermAcc d (pi (arg _ _ _) (el _ t₂)) = convTermAcc (suc d) t₂
    convTermAcc d (lam v t) = left (unsupportedSyntax (lam v t))
    convTermAcc d (sort x)  = left (unsupportedSyntax (sort x))
    convTermAcc d unknown   = left (unsupportedSyntax (unknown))

    convArgsAcc : ℕ → List (Arg Term) → Error (∃₂ (λ k n → Vec (PTerm n) k))
    convArgsAcc d [] = right (0 , 0 , [])
    convArgsAcc d (arg visible _ t ∷ ts) with convArgsAcc d ts
    convArgsAcc d (arg visible r t ∷ ts) | left msg = left msg
    convArgsAcc d (arg visible r t ∷ ts) | right ps with convTermAcc d t
    convArgsAcc d (arg visible r t ∷ ts) | right ps | left msg = left msg
    convArgsAcc d (arg visible r t ∷ ts) | right (k , n₂ , ps) | right (n₁ , p)
      with matchTermAndVec p ps
    ... | (p′ , ps′) = right (suc k , max n₁ n₂ , p′ ∷ ps′)
    convArgsAcc d (arg _       _ _ ∷ ts) = convArgsAcc d ts

  convTerm : Term → Error (∃ PTerm)
  convTerm = convTermAcc 0

  splitTerm : ∀ {n} → PTerm n → List (PTerm n)
  splitTerm (con pimpl (t₁ ∷ t₂ ∷ [])) = t₁ ∷ splitTerm t₂
  splitTerm t = return t

  -- converts an agda term into a list of terms by splitting at each function
  -- symbol; note the order: the last element of the list will always be the
  -- conclusion of the funciton with the rest of the elements being the premises.
  convTerm′ : Term → Error (∃ (List ∘ PTerm))
  convTerm′ t with convTerm t
  convTerm′ t | left msg      = left msg
  convTerm′ t | right (n , p) = right (n , splitTerm p)

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
  mkRule : ∀ {m} → Name → Error (∃ (Rule m))
  mkRule {_} name with convTerm′ (convName name)
  mkRule {_} name | left msg = left msg
  mkRule {m} name | right ts = mkRule′ ts
    where
      mkRule′ : ∃ (List ∘ PTerm) → Error (∃ (Rule m))
      mkRule′ (n , xs) with initLast xs
      mkRule′ (n , .[]) | [] = left panic!
      mkRule′ (n , .(xs ++ x ∷ [])) | xs ∷ʳ' x = right (n , global (rdef name) x xs)

  mutual
    reify : Proof → Term
    reify (con (rvar i) ps) = var i []
    reify (con (rdef n) ps) with definition n
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
  HintDB = ∀ {m} → Rules m

  hintdb : List Name → HintDB
  hintdb l {m} = concatMap (fromError ∘ mkRule) l
    where
      fromError : {A : Set} → Error A → List A
      fromError = fromEither (const []) [_]

  mkArgs : ∀ {m} → List (PTerm m) → Rules m → Rules m
  mkArgs {m} ts rs = mkArgsAcc 0 ts ++ rs
    where
      mkArgsAcc : (i : ℕ) → List (PTerm m) → Rules m
      mkArgsAcc _ [] = []
      mkArgsAcc i (t ∷ ts) = (m , local (rvar i) t []) ∷ mkArgsAcc (suc i) ts

  ruleset : HintDB → Term → Maybe (∃ (λ m → Goal m × Rules m))
  ruleset rules type
    with convTerm type
  ... | left msg = nothing
  ... | right (n , gs)
    with reverse (splitTerm gs)
  ... | [] = nothing
  ... | (g ∷ args) = just (n , g , mkArgs args rules)

  auto : ℕ → HintDB → Term → Term
  auto depth rules type
    with convTerm type
  ... | left msg = quoteMsg msg
  ... | right (n , gs)
    with splitTerm gs
  ... | [] = quoteMsg panic!
  ... | (g ∷ args)
    with solveToDepth depth (mkArgs args (rules {n})) g
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
