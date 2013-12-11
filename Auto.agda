open import Function using (_$_; _∘_; flip)
open import Category.Monad
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.List using (List; []; _∷_; [_]; map; _++_; foldr; concatMap; length; InitLast; reverse; initLast; _∷ʳ'_; fromMaybe)
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
    MaybeMonad = Maybe.monad

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

  open import Prolog Name PName _≟-PName_ public renaming (Term to PTerm)
  open import Prolog.Show Name showName PName showPName _≟-PName_ public

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
      return (con pimpl (t₁ ∷ t₂ ∷ []))
    term2term _ = nothing

    -- For a given list of arguments we can convert these into the vector that is
    -- used by the Prolog `con` constructor.

    args2args : ∀ {n} → List Term → Maybe (∃ (Vec (PTerm n)))
    args2args {n} [] = just (0 , [])
    args2args {n} (t ∷ ts) = cons <$> term2term t ⊛ args2args ts
      where
        cons : PTerm n → ∃ (Vec (PTerm n)) → ∃ (Vec (PTerm n))
        cons t (k , ts) = suc k , t ∷ ts


  -- TODO currently this implementation does not work, as it will not allow you
  --      to construct rules that derive unapplied functions. The reason for this
  --      is that we split the rules at every arrow, and take all preceding the
  --      arrows as premises.
  --
  --      Solution: instead of `Maybe` delivering a rule, we have to deliver a list
  --      of rules, where at every arrow we decide whether we split the remainder off
  --      as a result, or whether we keep on producing premises.

  name2rule : ∀ {n} → Name → Maybe (List (Rule n))
  name2rule {n} name = list2rule ∘ reverse <$> (term2list (name2term name))
    where
      -- We're interested in the rules formed by our types, so we will create a
      -- term by checking the type associated with a name and then removing the
      -- type constructor `el`.

      name2term : Name → Term
      name2term = untype ∘ type

      -- We can convert Agda terms to a list of Prolog terms by splitting on the
      -- type arrows; this way the last element of the list will always be the
      -- conclusion with the rest of the elements being the premises.

      term2list : Term → Maybe (List (PTerm n))
      term2list (def f args) = [_] <$> term2term (def f args)
      term2list (pi (arg visible _ (el _ t₁)) (el _ t₂)) =
        term2term t₁ >>= λ t → term2list t₂ >>= λ ts → return (t ∷ ts)
      term2list _ = nothing

      -- Finally, we can convert it into a Prolog rule by splitting the list at
      -- its last element, and taking the init as the premises and the last element
      -- as the conclusion.

      list2rule : List (PTerm n) → List (Rule n)
      list2rule [] = []
      list2rule (t ∷ ts) = list2rule′ t ts
        where
          list2rule′ : PTerm n → List (PTerm n) → List (Rule n)
          list2rule′ conc [] = rule name conc [] ∷ []
          list2rule′ conc (t ∷ ts) = here ∷ further
            where
              here    = rule name conc (t ∷ ts)
              further = list2rule′ (con pimpl (t ∷ conc ∷ [])) ts
