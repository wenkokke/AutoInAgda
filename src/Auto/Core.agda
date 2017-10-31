open import Level                      using (Level)
open import Function                   using (_∘_; id; flip)
open import Data.Fin     as Fin        using (fromℕ)
open import Data.Nat     as Nat        using (ℕ; suc; zero; pred; _+_; _⊔_)
open import Data.Nat.Properties using (≤-decTotalOrder)
open import Data.List    as List       using (List; []; _∷_; [_]; concatMap; _++_; length; map)
open import Data.Vec     as Vec        using (Vec; []; _∷_; _∷ʳ_; reverse; initLast; toList)
open import Data.Product as Prod       using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe   as Maybe      using (Maybe; just; nothing; maybe)
open import Data.Sum     as Sum        using (_⊎_; inj₁; inj₂)
open import Data.Integer as Int        using (ℤ; -[1+_]; +_) renaming (_≟_ to _≟-Int_)
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary            using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Reflection renaming (Term to AgTerm; _≟_ to _≟-AgTerm_)

module Auto.Core where

  open DecTotalOrder ≤-decTotalOrder using (total)

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b Level.⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B


  -- define error messages that may occur when the `auto` function is
  -- called.
  data Message : Set where
    searchSpaceExhausted : Message
    unsupportedSyntax    : Message


  -- define our own instance of the error functor based on the either
  -- monad, and use it to propagate one of several error messages
  private
    Error : ∀ {a} (A : Set a) → Set a
    Error A = Message ⊎ A

    _⟨$⟩_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Error A → Error B
    f ⟨$⟩ inj₁ x = inj₁ x
    f ⟨$⟩ inj₂ y = inj₂ (f y)


  -- define term names for the term language we'll be using for proof
  -- search; we use standard Agda names, together with term-variables
  -- and Agda implications/function types.
  data TermName : Set₀ where
    name   : (n : Name) → TermName
    var    : (i : ℤ)    → TermName
    impl   : TermName

  tname-injective : ∀ {x y} → TermName.name x ≡ TermName.name y → x ≡ y
  tname-injective refl = refl

  tvar-injective : ∀ {i j} → TermName.var i ≡ TermName.var j → i ≡ j
  tvar-injective refl = refl

  _≟-TermName_ : (x y : TermName) → Dec (x ≡ y)
  (name x) ≟-TermName (name  y) with x ≟-Name y
  (name x) ≟-TermName (name .x) | yes refl = yes refl
  (name x) ≟-TermName (name  y) | no  x≠y  = no (x≠y ∘ tname-injective)
  (name _) ≟-TermName (var   _) = no (λ ())
  (name _) ≟-TermName (impl   ) = no (λ ())
  (var  _) ≟-TermName (name  _) = no (λ ())
  (var  i) ≟-TermName (var   j) with i ≟-Int j
  (var  i) ≟-TermName (var  .i) | yes refl = yes refl
  (var  i) ≟-TermName (var   j) | no i≠j = no (i≠j ∘ tvar-injective)
  (var  _) ≟-TermName (impl   ) = no (λ ())
  (impl  ) ≟-TermName (name  _) = no (λ ())
  (impl  ) ≟-TermName (var   _) = no (λ ())
  (impl  ) ≟-TermName (impl   ) = yes refl

  -- define rule names for the proof terms/rules that our proof search will
  -- return/use; we'll use standard Agda names, together with rule-variables.
  data RuleName : Set where
    name  : Name → RuleName
    var   : ℕ    → RuleName

  name-injective : ∀ {x y} → RuleName.name x ≡ name y → x ≡ y
  name-injective refl = refl

  rvar-injective : ∀ {x y} → RuleName.var x ≡ var y → x ≡ y
  rvar-injective refl = refl

  _≟-RuleName_ : (x y : RuleName) → Dec (x ≡ y)
  name x ≟-RuleName name y = map′ (cong name) name-injective (x ≟-Name y)
  name x ≟-RuleName var  y = no (λ ())
  var  x ≟-RuleName name y = no (λ ())
  var  x ≟-RuleName var  y = map′ (cong var) rvar-injective (x Nat.≟ y)

  -- now we can load the definitions from proof search
  open import ProofSearch RuleName TermName _≟-TermName_ Literal _≟-Lit_
    as PS public renaming (Term to PsTerm; module Extensible to PsExtensible)

  -- next up, converting the terms returned by Agda's reflection
  -- mechanism to terms in our proof search's language!


  -- dictionary for the treatment of variables in conversion from Agda
  -- terms to terms to be used in proof search.
  ConvertVar  : Set
  ConvertVar  = (depth index : ℕ) → ∃ PsTerm

  -- conversion dictionary for rule-terms, which turns every variable
  -- that is within the scope of the term (i.e. is defined within the
  -- term by lambda abstraction) into a variable, and every variable
  -- which is defined out of scope into a Skolem constant (which
  -- blocks unification).
  convertVar4Term : ConvertVar
  convertVar4Term = fromVar
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar d i with total i d
      fromVar d i | inj₁ i≤d = (suc (Δ i≤d) , var (fromℕ (Δ i≤d)))
      fromVar d i | inj₂ i>d = (0 , con (var (-[1+ Δ i>d ])) [])

  -- conversion dictionary for goal-terms, which turns all variables
  -- into Skolem constants which blocks all unification.
  convertVar4Goal : ConvertVar
  convertVar4Goal = fromVar
    where
      fromVar : (depth index : ℕ) → ∃ PsTerm
      fromVar d i with total i d
      fromVar d i | inj₁ i≤d = (0 , con (var (+ Δ i≤d)) [])
      fromVar d i | inj₂ i>d = (0 , con (var (-[1+ Δ i>d ])) [])


  -- helper function for converting definitions or constructors to
  -- proof terms.
  fromDefOrCon : (s : Name) → ∃[ n ] List (PsTerm n) → ∃ PsTerm
  fromDefOrCon f (n , ts) = n , con (name f) ts


  -- specialised function to convert literals of natural numbers
  -- (since they have a representation using Agda names)
  convertℕ : ∀ {k} → ℕ → PsTerm k
  convertℕ  zero   = con (name (quote zero)) []
  convertℕ (suc n) = con (name (quote suc)) (convertℕ n ∷ [])


  -- convert an Agda term to a term, abstracting over the treatment of
  -- variables with an explicit dictionary of the type `ConvertVar`---
  -- passing in `ConvertVar4Term` or `ConvertVar4Goal` will result in
  -- rule-terms or goal-terms, respectively.

  convert : ConvertVar → (depth : ℕ) → AgTerm → Error (∃ PsTerm)
  convertChildren :
    ConvertVar → ℕ → List (Arg AgTerm) → Error (∃[ n ] List (PsTerm n))


  convert cv d (lit (nat n)) = inj₂ (0 , convertℕ n)
  convert cv d (lit l)       = inj₂ (0 , lit l)
  convert cv d (var i [])    = inj₂ (cv d i)
  convert cv d (var i args)  = inj₁ unsupportedSyntax
  convert cv d (con c args)  = fromDefOrCon c ⟨$⟩ convertChildren cv d args
  convert cv d (def f args)  = fromDefOrCon f ⟨$⟩ convertChildren cv d args
  convert cv d (pi (arg (arg-info visible _) t₁) (abs _ t₂)) with convert cv d t₁ | convert cv (suc d) t₂
  ... | inj₁ msg | _        = inj₁ msg
  ... | _        | inj₁ msg = inj₁ msg
  ... | inj₂ (n₁ , p₁) | inj₂ (n₂ , p₂)
    with match p₁ p₂
  ... | (p₁′ , p₂′) = inj₂ (n₁ ⊔ n₂ , con impl (p₁′ ∷ p₂′ ∷ []))
  convert cv d (pi (arg _ _) (abs _ t₂)) = convert cv (suc d) t₂
  convert cv d (lam _ _)     = inj₁ unsupportedSyntax
  convert cv d (pat-lam _ _) = inj₁ unsupportedSyntax
  convert cv d (sort _)      = inj₁ unsupportedSyntax
  convert cv d unknown       = inj₁ unsupportedSyntax
  convert cv d (meta x args) = inj₁ unsupportedSyntax


  convertChildren cv d [] = inj₂ (0 , [])
  convertChildren cv d (arg (arg-info visible _) t ∷ ts)
    with convert cv d t | convertChildren cv d ts
  ... | inj₁ msg      | _              = inj₁ msg
  ... | _             | inj₁ msg       = inj₁ msg
  ... | inj₂ (m , p)  | inj₂ (n , ps) with match p ps
  ... | (p′ , ps′)                      = inj₂ (m ⊔ n , p′ ∷ ps′)
  convertChildren cv d (arg _ _ ∷ ts)   = convertChildren cv d ts


  -- convert an Agda term to a rule-term.
  agda2term : AgTerm → Error (∃ PsTerm)
  agda2term t = convert convertVar4Term 0 t


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
  agda2goal×premises : AgTerm → Error (∃ PsTerm × Rules)
  agda2goal×premises t with convert convertVar4Goal 0 t
  ... | inj₁ msg            = inj₁ msg
  ... | inj₂ (n , p)        with split p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = inj₂ ((n , goal) , toPremises (pred k) prems)
    where
      toPremises : ∀ {k} → ℕ → Vec (PsTerm n) k → Rules
      toPremises i [] = []
      toPremises i (t ∷ ts) = (n , rule (var i) t []) ∷ toPremises (pred i) ts




  -- convert an Agda name to an rule-term.
  name2term : Name → TC (Error (∃ PsTerm))
  name2term nm = bindTC (getType nm) (λ tp → returnTC (agda2term tp))



  -- convert an Agda name to a rule.
  name2ruleHelper : Name → (Error (∃ PsTerm)) → TC (Error (∃ Rule))
  name2ruleHelper nm name2term_nm with name2term_nm
  ... | inj₁ msg             = returnTC (inj₁ msg)
  ... | inj₂ (n , t)         with split t
  ... | (k , ts)             with initLast ts
  ... | (prems , concl , _)  =  returnTC (inj₂ (n , rule (name nm) concl (toList prems)))



  -- convert an Agda name to a rule.
  name2rule : Name → TC (Error (∃ Rule))
  name2rule nm = bindTC (name2term nm) (name2ruleHelper nm)



  -- function which reifies untyped proof terms (from the
  -- `ProofSearch` module) to untyped Agda terms.


  reify : Proof → TC AgTerm
  reifyChildren : List Proof → TC (List (Arg AgTerm))

  reify (con (var i) ps) = returnTC ((var i []))
  reify (con (name n) ps) =
    bindTC (getDefinition n) (λ
      { (function x) → bindTC (reifyChildren ps) (λ rc → returnTC (def n rc))
      ; (data-type pars cs) →  bindTC (reifyChildren ps) ((λ rc → returnTC (con n rc)))
      ; (record′ c _) → returnTC unknown
      ; (constructor′ d ) → returnTC unknown
      ; axiom → returnTC unknown
      ; primitive′ → returnTC unknown} )


  reifyChildren [] = returnTC []
  reifyChildren (p ∷ ps) =
    bindTC (reify p)
    (λ rp → bindTC (reifyChildren ps) (λ rcps → returnTC (toArg rp ∷ rcps)))
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
