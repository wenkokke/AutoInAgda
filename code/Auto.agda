open import Level using (Level)
open import Function using (_∘_; id)
open import Data.Fin as Fin using (fromℕ)
open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _⊔_; decTotalOrder)
open import Data.List as List using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Vec as Vec using (Vec; []; _∷_; _∷ʳ_; reverse; initLast; toList)
open import Data.Product as Prod using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer as Int using (ℤ; -[1+_]; +_) renaming (_≟_ to _≟-Int_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary as Rel
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)
open import Reflection renaming (Term to AgTerm; _≟_ to _≟-AgTerm_)

module Auto where

  open Rel.DecTotalOrder {{...}} using (total)
  open Rel.DecSetoid {{...}} using (_≟_)

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b Level.⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B


  -- define error messages that may occur when the `auto` function is
  -- called.
  data Message : Set where
    searchSpaceExhausted : Message
    unsupportedSyntax    : Message


  -- define our own instance of the error monad, based on the either
  -- monad, and use it to propagate one of several error messages
  private
    Error : ∀ {a} (A : Set a) → Set a
    Error A = Message ⊎ A

    _<$>_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Error A → Error B
    f <$> inj₁ x = inj₁ x
    f <$> inj₂ y = inj₂ (f y)


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
  -- mechanism to terms in our proof search's language!


  -- dictionary for the treatment of variables in conversion from Agda
  -- terms to terms to be used in proof search.
  record ConvertVar : Set where
    field
      fromVar : (depth index : ℕ) → ∃ PsTerm

  -- conversion dictionary for rule-terms, which turns every variable
  -- that is within the scope of the term (i.e. is defined within the
  -- term by lambda abstraction) into a variable, and every variable
  -- which is defined out of scope into a Skolem constant (which
  -- blocks unification).
  ConvertVar4Term : ConvertVar
  ConvertVar4Term = record { fromVar = fromVar }
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar d i with total i d
      fromVar d i | inj₁ i≤d = (suc (Δ i≤d) , var (fromℕ (Δ i≤d)))
      fromVar d i | inj₂ i>d = (0 , con (tvar (-[1+ Δ i>d ])) [])

  -- conversion dictionary for goal-terms, which turns all variables
  -- into Skolem constants which blocks all unification.
  ConvertVar4Goal : ConvertVar
  ConvertVar4Goal = record { fromVar = fromVar′ }
    where
      fromVar′ : (depth index : ℕ) → ∃ PsTerm
      fromVar′ d i with total i d
      fromVar′ d i | inj₁ i≤d = (0 , con (tvar (+ Δ i≤d)) [])
      fromVar′ d i | inj₂ i>d = (0 , con (tvar (-[1+ Δ i>d ])) [])


  -- helper function for converting definitions or constructors to
  -- proof terms.
  fromDefOrCon : (s : Name) → ∃[ n ] List (PsTerm n) → ∃ PsTerm
  fromDefOrCon f (n , ts) = n , con (name f) ts


  -- convert an Agda term to a term, abstracting over the treatment of
  -- variables with an explicit dictionary of the type `ConvertVar`---
  -- passing in `ConvertVar4Term` or `ConvertVar4Goal` will result in
  -- rule-terms or goal-terms, respectively.
  mutual
    convert : ConvertVar → (depth : ℕ) → AgTerm → Error (∃ PsTerm)
    convert dict d (var i [])   = inj₂ (ConvertVar.fromVar dict d i)
    convert dict d (var i args) = inj₁ unsupportedSyntax
    convert dict d (con c args) = fromDefOrCon c <$> convertChildren dict d args
    convert dict d (def f args) = fromDefOrCon f <$> convertChildren dict d args
    convert dict d (pi (arg (arg-info visible _) (el _ t₁)) (el _ t₂))
      with convert dict d t₁ | convert dict (suc d) t₂
    ... | inj₁ msg | _        = inj₁ msg
    ... | _        | inj₁ msg = inj₁ msg
    ... | inj₂ (n₁ , p₁) | inj₂ (n₂ , p₂)
      with match p₁ p₂
    ... | (p₁′ , p₂′) = inj₂ (n₁ ⊔ n₂ , con impl (p₁′ ∷ p₂′ ∷ []))
    convert dict d (pi (arg _ _) (el _ t₂)) = convert dict (suc d) t₂
    convert dict d (lam v t) = inj₁ unsupportedSyntax
    convert dict d (sort x)  = inj₁ unsupportedSyntax
    convert dict d unknown   = inj₁ unsupportedSyntax

    convertChildren : ConvertVar → ℕ → List (Arg AgTerm) → Error (∃[ n ] List (PsTerm n))
    convertChildren dict d [] = inj₂ (0 , [])
    convertChildren dict d (arg (arg-info visible _) t ∷ ts) with convert dict d t | convertChildren dict d ts
    ... | inj₁ msg      | _              = inj₁ msg
    ... | _             | inj₁ msg       = inj₁ msg
    ... | inj₂ (m , p)  | inj₂ (n , ps) with match p ps
    ... | (p′ , ps′)                      = inj₂ (m ⊔ n , p′ ∷ ps′)
    convertChildren dict d (arg _ _ ∷ ts)   = convertChildren dict d ts


  -- convert an Agda term to a rule-term.
  agda2term : AgTerm → Error (∃ PsTerm)
  agda2term t = convert ConvertVar4Term 0 t


  -- split a term at every occurrence of the `impl` constructor---
  -- equivalent to splitting at every occurrence of the _→_ symbol in
  -- an Agda term.
  split : ∀ {n} → PsTerm n → ∃[ k ] Vec (PsTerm n) (suc k)
  split (con impl (t₁ ∷ t₂ ∷ [])) = Prod.map suc (λ ts → t₁ ∷ ts) (split t₂)
  split t = zero , t ∷ []


  -- convert an Agda term to a goal-term, together with a `HintDB`
  -- representing the premises of the rule---this means that for a
  -- term of the type `A → B` this function will generate a goal of
  -- type `B` and a premise of type `A`.
  agda2goal×premises : AgTerm → Error (∃ PsTerm × HintDB)
  agda2goal×premises t with convert ConvertVar4Goal 0 t
  ... | inj₁ msg            = inj₁ msg
  ... | inj₂ (n , p)        with split p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = inj₂ ((n , goal) , toPremises 0 prems)
    where
      toPremises : ∀ {k} → ℕ → Vec (PsTerm n) k → HintDB
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (rvar i) t []) ∷ toPremises (suc i) ts


  -- convert an Agda name to an rule-term.
  name2term : Name → Error (∃ PsTerm)
  name2term = agda2term ∘ unel ∘ type
    where
      unel : Type → AgTerm
      unel (el _ t) = t


  -- convert an Agda name to a rule.
  name2rule : Name → Error (∃ Rule)
  name2rule nm with name2term nm
  ... | inj₁ msg             = inj₁ msg
  ... | inj₂ (n , t)         with split t
  ... | (k , ts)             with initLast ts
  ... | (prems , concl , _)  = inj₂ (n , rule (name nm) concl (toList prems))


  -- function which reifies untyped proof terms (from the
  -- `ProofSearch` module) to untyped Agda terms.
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
        toArg = arg (arg-info visible relevant)


  -- data-type `Exception` which is used to unquote error messages to
  -- the type-level so that `auto` can generate descriptive type-errors.

  data Exception : Message → Set where
    throw : (msg : Message) → Exception msg

  quoteError : Message → AgTerm
  quoteError (searchSpaceExhausted) = quoteTerm (throw searchSpaceExhausted)
  quoteError (unsupportedSyntax)    = quoteTerm (throw unsupportedSyntax)


  -- operator for adding rules to a HintDB based on an Agda name.

  infixl 5 _<<_

  _<<_ : HintDB → Name → HintDB
  db << n with name2rule n
  db << n | inj₁ msg = db
  db << n | inj₂ r   = db ++ [ r ]


  -- embedded `auto` tactic for computing Agda functions.

  auto : ℕ → HintDB → AgTerm → AgTerm
  auto depth rules type
    with agda2goal×premises type
  ... | inj₁ msg = quoteError msg
  ... | inj₂ ((n , g) , args)
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
