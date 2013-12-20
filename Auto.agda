open import Function using (_$_; _∘_; id; flip; const)
open import Category.Monad
open import Data.Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; compare; less; equal; greater) renaming (_⊔_ to max)
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
    pimpl : PName 2

  data RName : Set where
    rdef : Name → RName
    rvar  : ℕ → RName

  _≟-PName_ : ∀ {k} (x y : PName k) → Dec (x ≡ y)
  _≟-PName_ {.2}  pimpl       pimpl       = yes refl
  _≟-PName_ {.2} (pname x .2) pimpl       = no (λ ())
  _≟-PName_ {.2}  pimpl      (pname y .2) = no (λ ())
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
  showPName (pimpl) = "→"

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
  matchTerms {n₁} {n₂} = match {n₁} {n₂} {PTerm} {PTerm} injTermL injTermL
    where
      open Indexed IndexedTerm renaming (injectL to injTermL)

  matchTermAndList : ∀ {n₁ n₂} → PTerm n₁ → List (PTerm n₂) → PTerm (max n₁ n₂) × List (PTerm (max n₁ n₂))
  matchTermAndList {n₁} {n₂} = match {n₁} {n₂} {PTerm} {List ∘ PTerm} injTermL injListL
    where
      open Indexed IndexedTerm renaming (injectL to injTermL)
      open Indexed (IndexedList IndexedTerm) renaming (injectL to injListL)

  matchTermAndVec : ∀ {k n₁ n₂} → PTerm n₁ → Vec (PTerm n₂) k → PTerm (max n₁ n₂) × Vec (PTerm (max n₁ n₂)) k
  matchTermAndVec {k} {n₁} {n₂} = match {n₁} {n₂} {PTerm} {λ n₂ → Vec (PTerm n₂) k} injTermL injVecL
    where
      open Indexed IndexedTerm renaming (injectL to injTermL)
      open Indexed (IndexedVec IndexedTerm) renaming (injectL to injVecL)

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
  mkRule : Name → Error (∃ Rule)
  mkRule name with convTerm′ (convName name)
  mkRule name | left msg = left msg
  mkRule name | right ts = mkRule′ ts
    where
      mkRule′ : ∃ (List ∘ PTerm) → Error (∃ Rule)
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

  hintdb : List Name → Rules
  hintdb = concatMap (fromError ∘ mkRule)
    where
      fromError : {A : Set} → Error A → List A
      fromError = fromEither (const []) [_]

  mkArgs : ∀ {n} → List (PTerm n) → Rules → Rules
  mkArgs ts rs = mkArgsAcc 0 ts ++ rs
    where
      mkArgsAcc : ∀ {n} → (i : ℕ) → List (PTerm n) → Rules
      mkArgsAcc {_} _ [] = []
      mkArgsAcc {n} i (t ∷ ts) = (n , global (rvar i) t []) ∷ mkArgsAcc (suc i) ts


  frules : Rules → Term → Rules
  frules rules type
    with convTerm type
  ... | left msg = []
  ... | right (n , gs)
    with reverse (splitTerm gs)
  ... | [] = []
  ... | (g ∷ args) = mkArgs args rules

  auto : ℕ → Rules → Term → Term
  auto depth rules type
    with convTerm type
  ... | left msg = quoteMsg msg
  ... | right (n , gs)
    with splitTerm gs
  ... | [] = quoteMsg panic!
  ... | (g ∷ args)
    with (solveToDepth depth (mkArgs args rules) g)
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


{-
      goal : Error (∃ PTerm)
      goal = convTerm type

      result : Term
      result with goal
      result | left msg = quoteMsg msg
      result | right (n , g) with (solveToDepth depth rules g)
      result | right (_ , _) | [] = quoteMsg searchSpaceExhausted
      result | right (_ , _) | (_ , ap) ∷ _ with (toProof ap)
      result | right (_ , _) | (_ , ap) ∷ _ | nothing = unknown
      result | right (_ , _) | (_ , ap) ∷ _ | just p  = reify p
-}
