open import Function using (_$_; _∘_; flip)

open import Category.Monad

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.List using (List; []; _∷_; [_]; map; _++_; foldr; concatMap; length; InitLast; initLast; _∷ʳ'_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
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

  _≟-PName_ : ∀ {k} (x y : PName k) → Dec (x ≡ y)
  _≟-PName_ {k} (pname x .k) (pname  y .k) with x ≟-Name y
  _≟-PName_ {k} (pname x .k) (pname .x .k) | yes refl = yes refl
  _≟-PName_ {k} (pname x .k) (pname  y .k) | no  x≢y  = no (x≢y ∘ cong elim)
    where
    elim : ∀ {k} → PName k → Name
    elim {k} (pname n .k) = n

  -- Due to this functionality being unavailable and unimplementable in plain Agda
  -- we'll just have to postulate the existance of a show function for Agda names.
  -- Using this postulate we can then implement a show function for Prolog names.

  postulate
    showName : Name → String

  showPName : ∀ {n} → PName n → String
  showPName (pname n _) = showName n

  -- Now we can load the Prolog and Prolog.Show libraries.

  open import Prolog Name PName _≟-PName_ renaming (Term to PTerm)
  open import Prolog.Show Name showName PName showPName _≟-PName_

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
    -- Note: the current implementation does not handle variables yet, and so only
    -- allows rules with _only_ constructors, i.e. propositional logic.

    term2term : ∀ {n} → Term → Maybe (PTerm n)
    term2term (def f args) = def2term f <$> args2args (map unarg args)
      where
        def2term : ∀ {n} → Name → ∃ (Vec (PTerm n))  → PTerm n
        def2term f (k , ts) = con (pname f k) ts
    term2term _ = nothing

    -- For a given list of arguments we can convert these into the vector that is
    -- used by the Prolog `con` constructor.

    args2args : ∀ {n} → List Term → Maybe (∃ (Vec (PTerm n)))
    args2args {n} [] = just (0 , [])
    args2args {n} (t ∷ ts) = cons <$> term2term t ⊛ args2args ts
      where
        cons : PTerm n → ∃ (Vec (PTerm n)) → ∃ (Vec (PTerm n))
        cons t (k , ts) = suc k , t ∷ ts



  name2rule : ∀ {n} → Name → Maybe (Rule n)
  name2rule n = list2rule =<< term2list (name2term n)
    where

      -- We're interested in the rules formed by our types, so we will create a
      -- term by checking the type associated with a name and then removing the
      -- type constructor `el`.

      name2term : Name → Term
      name2term = untype ∘ type

      -- We can convert Agda terms to a list of Prolog terms by splitting on the
      -- type arrows; this way the last element of the list will always be the
      -- conclusion with the rest of the elements being the premises.

      term2list : ∀ {n} → Term → Maybe (List (PTerm n))
      term2list (def f args) = [_] <$> term2term (def f args)
      term2list (pi (arg visible relevant (el _ t₁)) (el _ t₂)) = _∷_ <$> term2term t₁ ⊛ term2list t₂
      term2list _ = nothing

      -- Finally, we can convert it into a Prolog rule by splitting the list at
      -- its last element, and taking the init as the premises and the last element
      -- as the conclusion.

      list2rule : ∀ {n} → List (PTerm n) → Maybe (Rule n)
      list2rule xs with initLast xs
      list2rule .[] | [] = nothing
      list2rule .(xs ++ x ∷ []) | xs ∷ʳ' x = just (rule n x xs)
