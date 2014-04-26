open import Level using (Level)
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
open import Data.Product as Prod using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.String using (String)
open import Data.Sum as Sum using () renaming (_⊎_ to Either; inj₁ to left; inj₂ to right; [_,_] to fromEither)
open import Data.Integer as Int using (ℤ; -[1+_]; +_) renaming (_≟_ to _≟-Int_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Reflection renaming (Term to AgTerm; _≟_ to _≟-AgTerm_)

module Auto where

  open DecSetoid {{...}} using (_≟_)

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b Level.⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B


  -- define our own instance of the error monad, based on the either
  -- monad, and use it to propagate one of several error messages

  data Message : Set where
    searchSpaceExhausted : Message
    unsupportedSyntax    : Message

  private
    Error : ∀ {a} (A : Set a) → Set a
    Error A = Either Message A

    _<$>_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Error A → Error B
    f <$> left  x = left x
    f <$> right y = right (f y)

  -- define term names for the term language we'll be using for proof
  -- search; we use standard Agda names, together with term-variables
  -- and Agda implications/function types.

  data TermName : Set where
    name : (n : Name) → TermName
    tvar : (i : ℤ) → TermName
    impl : TermName

  pname-inj : ∀ {x y} → name x ≡ name y → x ≡ y
  pname-inj refl = refl

  pvar-inj : ∀ {i j} → tvar i ≡ tvar j → i ≡ j
  pvar-inj refl = refl

  _≟-TermName_ : (x y : TermName) → Dec (x ≡ y)
  _≟-TermName_ (name x) (name  y) with x ≟-Name y
  _≟-TermName_ (name x) (name .x) | yes refl = yes refl
  _≟-TermName_ (name x) (name  y) | no  x≠y  = no (x≠y ∘ pname-inj)
  _≟-TermName_ (name _) (tvar _)  = no (λ ())
  _≟-TermName_ (name _)  impl     = no (λ ())
  _≟-TermName_ (tvar _) (name _)  = no (λ ())
  _≟-TermName_ (tvar i) (tvar  j) with i ≟-Int j
  _≟-TermName_ (tvar i) (tvar .i) | yes refl = yes refl
  _≟-TermName_ (tvar i) (tvar  j) | no i≠j = no (i≠j ∘ pvar-inj)
  _≟-TermName_ (tvar _)  impl     = no (λ ())
  _≟-TermName_  impl    (name _)  = no (λ ())
  _≟-TermName_  impl    (tvar _)  = no (λ ())
  _≟-TermName_  impl     impl     = yes refl


  -- define rule names for the proof terms/rules that our proof search will
  -- return/use; we'll use standard Agda names, together with rule-variables.

  data RuleName : Set where
    name : Name → RuleName
    rvar : ℕ → RuleName


  -- now we can load the definitions from proof search

  open import ProofSearch RuleName TermName _≟-TermName_ as PS public
       renaming (Term to PsTerm)


  -- next up, converting the terms returned by Agda's reflection
  -- mechanism to terms in our proof search's language.

  -- first off, we'll implement a few basic functions to ease our
  -- working with Agda's reflection library.

  unarg : ∀ {A} → Arg A → A
  unarg (arg _ _ x) = x

  unel : Type → AgTerm
  unel (el _ t) = t

  -- We'll need the function below later on, when we try to convert found
  -- variables to finitely indexed variables within our domain `n`.

  fromDefOrCon : (s : Name) → ∃[ n ] List (PsTerm n) → ∃ PsTerm
  fromDefOrCon f (n , ts) = n , con (name f) ts

  record FromVar : Set where
    field
      fromVar : (depth index : ℕ) → ∃ PsTerm

  FromVarTerm : FromVar
  FromVarTerm = record { fromVar = fromVar }
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar  d i with compare d i
      fromVar  d .(suc (d + k)) | less    .d k = (0     , con (tvar (-[1+ k ])) [])
      fromVar .i i              | equal   .i   = (1     , var zero)
      fromVar .(suc (i + k)) i  | greater .i k = (suc k , var (Fin.fromℕ k))

  FromVarGoal : FromVar
  FromVarGoal = record { fromVar = fromVar′ }
    where
      fromVar′ : (depth index : ℕ) → ∃ PsTerm
      fromVar′  d i with compare d i
      fromVar′  d .(suc (d + k)) | less    .d k = (0 , con (tvar (-[1+ k ])) [])
      fromVar′ .i i              | equal   .i   = (0 , con (tvar (+ 0)) [])
      fromVar′ .(suc (i + k)) i  | greater .i k = (0 , con (tvar (+ k)) [])

  second : ∀ {A B C : Set} → (B → C) → A × B → A × C
  second f (x , y) = (x , f y)

  splitTerm : ∀ {n} → PsTerm n → ∃[ k ] Vec (PsTerm n) (suc k)
  splitTerm (con impl (t₁ ∷ t₂ ∷ [])) = Prod.map suc (λ ts → t₁ ∷ ts) (splitTerm t₂)
  splitTerm t = zero , t ∷ []

  mutual
    convertTerm : FromVar → ℕ → AgTerm → Error (∃ PsTerm)
    convertTerm dict d (var i [])   = right (FromVar.fromVar dict d i)
    convertTerm dict d (var i args) = left unsupportedSyntax
    convertTerm dict d (con c args) = fromDefOrCon c <$> convertArgs dict d args
    convertTerm dict d (def f args) = fromDefOrCon f <$> convertArgs dict d args
    convertTerm dict d (pi (arg visible _ (el _ t₁)) (el _ t₂))
      with convertTerm dict d t₁ | convertTerm dict (suc d) t₂
    ... | left msg | _        = left msg
    ... | _        | left msg = left msg
    ... | right (n₁ , p₁) | right (n₂ , p₂)
      with match p₁ p₂
    ... | (p₁′ , p₂′) = right (n₁ ⊔ n₂ , con impl (p₁′ ∷ p₂′ ∷ []))
    convertTerm dict d (pi (arg _ _ _) (el _ t₂)) = convertTerm dict (suc d) t₂
    convertTerm dict d (lam v t) = left unsupportedSyntax
    convertTerm dict d (sort x)  = left unsupportedSyntax
    convertTerm dict d unknown   = left unsupportedSyntax

    convertArgs : FromVar → ℕ → List (Arg AgTerm) → Error (∃[ n ] List (PsTerm n))
    convertArgs dict d [] = right (0 , [])
    convertArgs dict d (arg visible _ t ∷ ts) with convertTerm dict d t | convertArgs dict d ts
    ... | left msg       | _              = left msg
    ... | _              | left msg       = left msg
    ... | right (m , p)  | right (n , ps) with match p ps
    ... | (p′ , ps′)                      = right (m ⊔ n , p′ ∷ ps′)
    convertArgs dict d (arg _ _ _ ∷ ts)   = convertArgs dict d ts

  toTerm : AgTerm → Error (∃ PsTerm)
  toTerm t = convertTerm FromVarTerm 0 t

  toGoalAndPremises : AgTerm → Error (∃ PsTerm × HintDB)
  toGoalAndPremises t with convertTerm FromVarGoal 0 t
  ... | left msg            = left msg
  ... | right (n , p)       with splitTerm p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = right ((n , goal) , toPremises 0 prems)
    where
      toPremises : ∀ {k} → ℕ → Vec (PsTerm n) k → HintDB
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (rvar i) t []) ∷ toPremises (suc i) ts

  fromName : Name → Error (∃ PsTerm)
  fromName = toTerm ∘ unel ∘ type

  toRule : Name → Error (∃ Rule)
  toRule nm with fromName nm
  ... | left msg             = left msg
  ... | right (n , t)        with splitTerm t
  ... | (k , ts)             with initLast ts
  ... | (prems , concl , _)  = right (n , rule (name nm) concl (toList prems))

  mutual
    reify : Proof → AgTerm
    reify (con (rvar i) ps) = var i []
    reify (con (name n) ps) with definition n
    ... | function x   = def n (reifyChildren ps)
    ... | constructor′ = con n (reifyChildren ps)
    ... | data-type x  = unknown
    ... | record′ x    = unknown
    ... | axiom        = unknown
    ... | primitive′   = unknown

    reifyChildren : List Proof → List (Arg AgTerm)
    reifyChildren [] = []
    reifyChildren (p ∷ ps) = toArg (reify p) ∷ reifyChildren ps
      where
        toArg : AgTerm → Arg AgTerm
        toArg = arg visible relevant

  data Exception : Message → Set where
    throw : (msg : Message) → Exception msg

  quoteError : Message → AgTerm
  quoteError (searchSpaceExhausted) = quoteTerm (throw searchSpaceExhausted)
  quoteError (unsupportedSyntax)    = quoteTerm (throw unsupportedSyntax)

  infixl 5 _<<_

  _<<_ : HintDB → Name → HintDB
  db << n with toRule n
  db << n | left msg = db
  db << n | right r  = db ++ [ r ]

  auto : ℕ → HintDB → AgTerm → AgTerm
  auto depth rules type
    with toGoalAndPremises type
  ... | left msg = quoteError msg
  ... | right ((n , g) , args)
    with dfs depth (solve g (args ++ rules))
  ... | []      = quoteError searchSpaceExhausted
  ... | (p ∷ _) = intros (reify p)
    where
      intros : AgTerm → AgTerm
      intros = introsAcc (length args)
        where
          introsAcc : ℕ → AgTerm → AgTerm
          introsAcc  zero   t = t
          introsAcc (suc k) t = lam visible (introsAcc k t)
