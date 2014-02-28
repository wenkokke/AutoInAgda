open import Level using (Level) renaming (suc to lsuc; zero to lzero)
open import Function using (_$_; _∘_; id; flip; const)
open import Category.Applicative
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin; suc; zero; #_)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; compare; less; equal; greater)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Vec as Vec using (Vec; []; _∷_; _∷ʳ_; reverse; initLast; toList)
open import Data.Product as Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.String using (String)
open import Data.Sum as Sum using () renaming (_⊎_ to Either; inj₁ to left; inj₂ to right; [_,_] to fromEither)
open import Data.Integer as Int using (ℤ; -[1+_]; +_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Reflection renaming (_≟-Name_ to decEqName; _≟_ to decEqTerm)

module Auto where

  -- open up the classes we'll be using
  private
    open RawApplicative {{...}} renaming (_⊛_ to _⟨*⟩_; _<$>_ to _⟨$⟩_)
    open DecSetoid {{...}} using (_≟_)
    NameDecSetoid  = PropEq.decSetoid decEqName
    NatDecSetoid   = PropEq.decSetoid Nat._≟_
    IntDecSetoid   = Int.decSetoid

  data Message : Set where
    searchSpaceExhausted : Message
    unsupportedSyntax    : Message
    panic!               : Message

  Error : ∀ {a} (A : Set a) → Set a
  Error A = Either Message A

  AppError : ∀ {f} → RawApplicative (Error {a = f})
  AppError = record { pure = right ; _⊛_ = _⊛_ }
    where
      _⊛_ : ∀ {a b} {A : Set a} {B : Set b} → Error (A → B) → Error A → Error B
      left  m ⊛ _        = left m
      right f ⊛ left  m  = left m
      right f ⊛ right x  = right (f x)

  data TermName : Set where
    pname : (n : Name) → TermName
    pvar  : (i : ℤ) → TermName
    pimpl : TermName

  agdaTypeArity : Type → ℕ
  agdaTypeArity (el _ (pi _ t)) = suc (agdaTypeArity t)
  agdaTypeArity (el _ t)        = zero

  agdaNameArity : Name → ℕ
  agdaNameArity n = agdaTypeArity (type n)

  prologNameArity : TermName → ℕ
  prologNameArity (pname n) = agdaNameArity n
  prologNameArity (pvar _)  = 0
  prologNameArity (pimpl)   = 2

  pname-injective : ∀ {x y} → pname x ≡ pname y → x ≡ y
  pname-injective refl = refl

  pvar-injective : ∀ {i j} → pvar i ≡ pvar j → i ≡ j
  pvar-injective refl = refl

  decEqTermName : (x y : TermName) → Dec (x ≡ y)
  decEqTermName (pname x) (pname  y) with x ≟ y
  decEqTermName (pname x) (pname .x) | yes refl = yes refl
  decEqTermName (pname x) (pname  y) | no  x≢y  = no (x≢y ∘ pname-injective)
  decEqTermName (pname _) (pvar _)   = no (λ ())
  decEqTermName (pname _)  pimpl     = no (λ ())
  decEqTermName (pvar _)  (pname _)  = no (λ ())
  decEqTermName (pvar i)  (pvar  j)  with i ≟ j
  decEqTermName (pvar i)  (pvar .i)  | yes refl = yes refl
  decEqTermName (pvar i)  (pvar  j)  | no i≢j = no (i≢j ∘ pvar-injective)
  decEqTermName (pvar _)   pimpl     = no (λ ())
  decEqTermName  pimpl    (pname _)  = no (λ ())
  decEqTermName  pimpl    (pvar _)   = no (λ ())
  decEqTermName  pimpl     pimpl     = yes refl

  private
    TermNameDecSetoid = PropEq.decSetoid decEqTermName

  data RuleName : Set where
    rname : Name → RuleName
    rvar  : ℕ → RuleName

  -- Due to this functionality being unavailable and unimplementable in plain Agda
  -- we'll just have to postulate the existance of a show function for Agda names.
  -- Using this postulate we can then implement a show function for Prolog names.

  -- Now we can load the Prolog libraries.

  open import Prolog RuleName TermName decEqTermName as PI public

  -- We'll implement a few basic functions to ease our working with Agda's
  -- Reflection library.

  unarg : ∀ {A} → Arg A → A
  unarg (arg _ _ x) = x

  unel : Type → Term
  unel (el _ t) = t

  -- We'll need the function below later on, when we try to convert found
  -- variables to finitely indexed variables within our domain `n`.

  fromDefOrCon : (s : Name) → ∃ (λ n → List (PrologTerm n)) → ∃ PrologTerm
  fromDefOrCon f (n , ts) = n , con (pname f) ts

  record Case : Set where
    field
      fromVar : ℕ → ℕ → ∃  PrologTerm
      fromCon : (s : Name) → ∃ (λ n → List (PrologTerm n)) → ∃ PrologTerm
      fromDef : (s : Name) → ∃ (λ n → List (PrologTerm n)) → ∃ PrologTerm

  CaseTerm : Case
  CaseTerm = record { fromVar = fromVar ; fromCon = fromDefOrCon ; fromDef = fromDefOrCon  }
    where
      fromVar : ℕ → ℕ → ∃ PrologTerm
      fromVar  d i with compare d i
      fromVar  d .(suc (d + k)) | less    .d k = (0     , con (pvar (-[1+ k ])) [])
      fromVar .i i              | equal   .i   = (1     , var zero)
      fromVar .(suc (i + k)) i  | greater .i k = (suc k , var (Fin.fromℕ k))

  CaseGoal : Case
  CaseGoal = record { fromVar = fromVar′ ; fromCon = fromDefOrCon ; fromDef = fromDefOrCon }
    where
      fromVar′ : ℕ → ℕ → ∃ PrologTerm
      fromVar′  d i with compare d i
      fromVar′  d .(suc (d + k)) | less    .d k = (0 , con (pvar (-[1+ k ])) [])
      fromVar′ .i i              | equal   .i   = (0 , con (pvar (+ 0)) [])
      fromVar′ .(suc (i + k)) i  | greater .i k = (0 , con (pvar (+ k)) [])

  second : ∀ {A B C : Set} → (B → C) → A × B → A × C
  second f (x , y) = (x , f y)

  splitTerm : ∀ {n} → PrologTerm n → ∃ (λ k → Vec (PrologTerm n) (suc k))
  splitTerm (con pimpl (t₁ ∷ t₂ ∷ [])) = Product.map suc (λ ts → t₁ ∷ ts) (splitTerm t₂)
  splitTerm t = zero , t ∷ []

  mutual
    convertTerm : Case → ℕ → Term → Error (∃ PrologTerm)
    convertTerm dict d (var i [])   = pure (Case.fromVar dict d i)
    convertTerm dict d (var i args) = left unsupportedSyntax
    convertTerm dict d (con c args) = Case.fromCon dict c ⟨$⟩ convertArgs dict d args
    convertTerm dict d (def f args) = Case.fromDef dict f ⟨$⟩ convertArgs dict d args
    convertTerm dict d (pi (arg visible _ (el _ t₁)) (el _ t₂))
      with convertTerm dict d t₁ | convertTerm dict (suc d) t₂
    ... | left msg | _        = left msg
    ... | _        | left msg = left msg
    ... | right (n₁ , p₁) | right (n₂ , p₂)
      with matchTerms p₁ p₂
    ... | (p₁′ , p₂′) = right (n₁ ⊔ n₂ , con pimpl (p₁′ ∷ p₂′ ∷ []))
    convertTerm dict d (pi (arg _ _ _) (el _ t₂)) = convertTerm dict (suc d) t₂
    convertTerm dict d (lam v t) = left unsupportedSyntax
    convertTerm dict d (sort x)  = left unsupportedSyntax
    convertTerm dict d unknown   = left unsupportedSyntax

    convertArgs : Case → ℕ → List (Arg Term) → Error (∃ (λ n → List (PrologTerm n)))
    convertArgs dict d [] = right (0 , [])
    convertArgs dict d (arg visible _ t ∷ ts) with convertTerm dict d t | convertArgs dict d ts
    ... | left msg       | _              = left msg
    ... | _              | left msg       = left msg
    ... | right (m , p)  | right (n , ps) with matchTermAndList p ps
    ... | (p′ , ps′)                      = right (m ⊔ n , p′ ∷ ps′)
    convertArgs dict d (arg _ _ _ ∷ ts) = convertArgs dict d ts

  toTerm : Term → Error (∃ PrologTerm)
  toTerm t = convertTerm CaseTerm 0 t

  toGoalAndPremises : Term → Error (∃ PrologTerm × Rules)
  toGoalAndPremises t with convertTerm CaseGoal 0 t
  ... | left msg            = left msg
  ... | right (n , p)       with splitTerm p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = right ((n , goal) , toPremises 0 prems)
    where
      toPremises : ∀ {k} → ℕ → Vec (PrologTerm n) k → Rules
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (rvar i) t []) ∷ toPremises (suc i) ts

  fromName : Name → Error (∃ PrologTerm)
  fromName = toTerm ∘ unel ∘ type

  toRule : Name → Error (∃ Rule)
  toRule name with fromName name
  ... | left msg             = left msg
  ... | right (n , t)        with splitTerm t
  ... | (k , ts)             with initLast ts
  ... | (prems , concl , _)  = right (n , rule (rname name) concl (toList prems))

  mutual
    reify : ProofTerm → Term
    reify (con (rvar i) ps) = var i []
    reify (con (rname n) ps) with definition n
    ... | function x   = def n (reifyChildren ps)
    ... | constructor′ = con n (reifyChildren ps)
    ... | data-type x  = unknown
    ... | record′ x    = unknown
    ... | axiom        = unknown
    ... | primitive′   = unknown

    reifyChildren : List ProofTerm → List (Arg Term)
    reifyChildren [] = []
    reifyChildren (p ∷ ps) = toArg (reify p) ∷ reifyChildren ps
      where
        toArg : Term → Arg Term
        toArg = arg visible relevant

  data Exception : Message → Set where
    throw : (msg : Message) → Exception msg

  quoteError : Message → Term
  quoteError (searchSpaceExhausted) = quoteTerm (throw searchSpaceExhausted)
  quoteError (unsupportedSyntax)    = quoteTerm (throw unsupportedSyntax)
  quoteError (panic!)               = quoteTerm (throw panic!)

  HintDB : Set
  HintDB = List (∃ Rule)

  all : {A : Set} {P : A -> Set} -> List A -> Set
  all [] = ⊤
  all {P = P} (x ∷ xs) = P x × all {P = P} xs

  isRight : {A B : Set} -> Either A B -> Set
  isRight (left _)   = ⊥
  isRight (right _)  = ⊤

  fromRight : {A : Set} -> (x : Error A) -> {p : isRight x} -> A
  fromRight (left x) {()} 
  fromRight (right y) = y

  hintdb : (nms : List Name) → {p : all {Name} {\nm -> isRight (toRule nm)} nms} -> HintDB
  hintdb [] = []
  hintdb (nm ∷ nms) {p , ps} = (fromRight (toRule nm) {p}) ∷ hintdb nms {ps}

  infixl 5 _<<_

  _<<_ : HintDB → Name → HintDB
  db << n with toRule n
  db << n | left msg = db
  db << n | right r  = db ++ [ r ]

  auto : ℕ → HintDB → Term → Term
  auto depth rules type
    with toGoalAndPremises type
  ... | left msg = quoteError msg
  ... | right ((n , g) , args)
    with searchToDepth depth (args ++ rules) g
  ... | [] = quoteError searchSpaceExhausted
  ... | (_ , ap) ∷ _
    with toProofTerm ap
  ... | nothing = quoteError panic!
  ... | just p  = intros (reify p)
    where
      intros : Term → Term
      intros = introsAcc (length args)
        where
          introsAcc : ℕ → Term → Term
          introsAcc  zero   t = t
          introsAcc (suc k) t = lam visible (introsAcc k t)
