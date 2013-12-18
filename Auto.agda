open import Function using (_$_; _∘_; flip)
open import Category.Monad
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.List as List
  using (List; []; _∷_; [_]; map; _++_; foldr; concatMap; length; InitLast; reverse; initLast; _∷ʳ'_; fromMaybe)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong)
open import Reflection

module Auto where

  -- open up the classes we'll be using
  private
    open RawMonad {{...}}
    MonadMaybe = Maybe.monad
    MonadList  = List.monad

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
    showName : Name → String

  showPName : ∀ {n} → PName n → String
  showPName (pname n _) = showName n
  showPName (impl) = "→"

  -- Now we can load the Prolog and Prolog.Show libraries.

  import Prolog
  module PI = Prolog Name PName _≟-PName_
  open PI public
    using (Rules; Rule; rule; conclusion; premises; Proof; var; con
          ; solveToDepth; toProof)
    renaming (Term to PTerm)

  import Prolog.Show
  module PSI = Prolog.Show Name showName PName showPName _≟-PName_

  -- We'll implement a few basic functions to ease our working with Agda's
  -- Reflection library.

  unarg : ∀ {A} → Arg A → A
  unarg (arg _ _ x) = x

  untype : Type → Term
  untype (el _ t) = t

  -- We'll need the function below later on, when we try to convert found
  -- variables to finitely indexed variables within our domain `n`.

  toFin : (m n : ℕ) → Maybe (Fin m)
  toFin  zero    zero   = nothing
  toFin  zero   (suc n) = nothing
  toFin (suc m)  zero   = just zero
  toFin (suc m) (suc n) = suc <$> toFin m n

  {-# NO_TERMINATION_CHECK #-}
  mutual

    -- We can convert Agda terms to Prolog terms simply by rewriting definitions
    -- into Prolog predicates.
    --
    -- TODO the current implementation does not handle variables yet, and so only
    --      allows rules with _only_ constructors, i.e. propositional logic.
    -- TODO Since _→_ is part of the Agda syntax (as `pi`) it has no corresponding
    --      Agda name. Therefore we cannot represent it in Agda.
    --      Solved by introducing the `impl` constructor for `PName`.

    term2term : ∀ {n} → Term → Maybe (PTerm n)
    term2term (def f args) = def2term f <$> args2args (map unarg args)
      where
        def2term : ∀ {n} → Name → ∃ (Vec (PTerm n))  → PTerm n
        def2term f (k , ts) = con (pname f k) ts
    term2term (pi (arg visible _ (el _ t₁)) (el _ t₂)) =
      term2term t₁ >>= λ t₁ →
      term2term t₂ >>= λ t₂ →
      return (con pimpl (t₂ ∷ t₁ ∷ []))
    term2term _ = nothing

    -- For a given list of arguments we can convert these into the vector that is
    -- used by the Prolog `con` constructor.

    args2args : ∀ {n} → List Term → Maybe (∃ (Vec (PTerm n)))
    args2args {n} [] = just (0 , [])
    args2args {n} (t ∷ ts) = cons <$> term2term t ⊛ args2args ts
      where
        cons : PTerm n → ∃ (Vec (PTerm n)) → ∃ (Vec (PTerm n))
        cons t (k , ts) = suc k , t ∷ ts


  -- We're interested in the rules formed by our types, so we will create a
  -- term by checking the type associated with a name and then removing the
  -- type constructor `el`.
  name2term : Name → Term
  name2term = untype ∘ type

  Apply : Rule 2
  Apply = rule (quote _$_) (var B)
                         ( (con pimpl (var B ∷ var A ∷ []))
                         ∷ (var A)
                         ∷ [])
    where
      A B : Fin 2
      A = zero
      B = suc zero

  Compose : Rule 3
  Compose = rule (quote _∘_) (con pimpl (var C ∷ var A ∷ []))
                           ( (con pimpl (var C ∷ var B ∷ []))
                           ∷ (con pimpl (var B ∷ var A ∷ []))
                           ∷ [])
    where
      A B C : Fin 3
      A = zero
      B = suc zero
      C = suc (suc zero)

  -- term2list:
  --  converts an agda term into a list of terms by splitting at each function
  --  symbol; note the order: the last element of the list will always be the
  --  conclusion of the funciton with the rest of the elements being the premises.
  term2list : Term → Maybe (List (PTerm 0))
  term2list (def f args) = [_] <$> term2term (def f args)
  term2list (pi (arg visible _ (el _ t₁)) (el _ t₂)) =
    term2term t₁ >>= λ t → term2list t₂ >>= λ ts → return (t ∷ ts)
  term2list _ = nothing

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
  name2rule : Name → Maybe (∃ Rule)
  name2rule name = list2rule =<< term2list (name2term name)
    where
      list2rule : List (PTerm 0) → Maybe (∃ Rule)
      list2rule ts with initLast ts
      list2rule .[]             | []       = nothing
      list2rule .(ts ++ t ∷ []) | ts ∷ʳ' t = just (0 , rule name t ts)

  -- name2rule′:
  --   converts names into a list of rules, where each generated rule represents
  --   one way of splitting the function type into a prolog rule; for instance,
  --   the rule for function composition will split into four separate rules
  --   due to the presence of three top-level function symbols.
  --
  --     1. C :- A, A → B, B → C.
  --     2. A → C :- A → B, B → C.
  --     3. (A → B) → A → C :- B → C.
  --     4. (B → C) → (A → B) → A → C) :- .
  --
  name2rule′ : Name → Maybe (List (∃ Rule))
  name2rule′ name = list2rules ∘ reverse <$> (term2list (name2term name))
    where
      -- we can convert a list of terms to a list of prolog rules by reversing the
      -- list, and then splitting off a new rule at every cons, either keeping the
      -- rest of the list as premises or taking the rules produced by the recursive
      -- application of this conversion after replacing a function symbol.
      list2rules : List (PTerm 0) → List (∃ Rule)
      list2rules [] = []
      list2rules (t ∷ ts) = list2rules′ t ts
        where
          list2rules′ : PTerm 0 → List (PTerm 0) → List (∃ Rule)
          list2rules′ conc [] = (0 , rule name conc []) ∷ []
          list2rules′ conc (t ∷ ts) = here ∷ further
            where
              here    = 0 , rule name conc (t ∷ ts)
              further = list2rules′ (con pimpl (t ∷ conc ∷ [])) ts


  -- name2rule″
  --   converts name into a single rule, where the entire rule is only capable
  --   of inferring the entire function type; for instance, for function composition
  --   we will get the following rule:
  --
  --     (B → C) → (A → B) → A → C) :- .
  --
  --  for this conversion strategy to work at all we need to add an inference rule
  --  for function application (which would be unavailable when using only this)a
  --  conversion strategy, but can be obtained by applying the first strategy
  --  (name2rule) to the function application symbol (_$_) or added manually as:
  --
  --    B :- A, A → B.
  --
  name2rule″ : Name → Maybe (∃ Rule)
  name2rule″ n = (λ t → 0 , rule n t []) <$> term2term (name2term n)

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
      goal : Maybe (PTerm 0)
      goal = term2term type

      rules : Rules
      rules = concatMap (fromMaybe ∘ name2rule) names

      result : Term
      result with goal
      result | nothing = unknown
      result | just g with (solveToDepth depth rules g)
      result | just _ | [] = unknown
      result | just _ | (_ , ap) ∷ _ with (toProof ap)
      result | just _ | (_ , ap) ∷ _ | nothing = unknown
      result | just _ | (_ , ap) ∷ _ | just p  = reify p
