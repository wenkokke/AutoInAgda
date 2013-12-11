open import Auto
open import Function using (_$_)
open import Category.Functor
open import Category.Monad
open import Data.Bin as Bin using (Bin)
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; _∷_; []; concat; concatMap; fromMaybe)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (∃; _,_)
open import Data.String using (String)

module Auto.Example where

  -- At the moment, the following rule does not yet compile (i.e. it
  -- produces `nothing`) as the `Fin` datatype is indexed by a variable,
  -- and first-order datatypes are not yet supported.

  fin2nat : ∀ {n} → Maybe (List (Rule n))
  fin2nat = name2rule (quote Fin.toℕ)

  -- However, the `show` function for ℕ is supported, as it a simple
  -- propositional type.

  nat2str : ∀ {n} → Maybe (List (Rule n))
  nat2str = name2rule (quote showℕ)

  -- The same holds for the successor function on ℕ. The difference is that
  -- the `suc` function is a constructor.

  bin2nat : ∀ {n} → Maybe (List (Rule n))
  bin2nat = name2rule (quote Bin.toℕ)

  -- Finally, we can also create a rule for function composition. There is
  -- one catch, though. We have to instantiate the types.

  _∘_ : (ℕ → String) → (Bin → ℕ) → (Bin → String)
  _∘_ g f x = g (f x)

  compose : ∀ {n} → Maybe (List (Rule n))
  compose = name2rule (quote _∘_)

  -- A general note; the current type for the conversion functions `name2rule`
  -- and `term2term` is rather short-sighted, as they allow the function to determine
  -- its own number of arguments. Instead, this should be left existentially quantified
  -- as a rule obviously needs to be able to determine its own number of arguments.
  -- For the time being, we'll rely on a number of helper functions to construct the ruleset
  -- out of these "potential" rules.

  ex : (∀ {n} → Maybe (List (Rule n))) → Maybe (List (∃ Rule))
  ex m = (λ ls → (λ r → 0 , r) <$> ls) <$>  m
    where
      open RawMonad {{...}}
      MonadMaybe = Maybe.monad
      MonadList  = List.monad

  catMaybes : ∀ {α} {A : Set α} → List (Maybe A) → List A
  catMaybes = concatMap fromMaybe

  -- We can construct a ruleset out of all the rules that compile (though I
  -- should probably look into a method for emitting a warning when a rule
  -- does not produce a valid rule).

  rules : Rules
  rules = concat $ catMaybes (ex fin2nat ∷ ex nat2str ∷ ex bin2nat ∷ ex compose ∷ [])

  -- Finally we can see if Agda knows how to compute a term of type `Bin → String`,
  -- using the set of rules that we have given it.

  goal : Maybe (PTerm 0)
  goal = term2term (quoteTerm (Bin → String))

  main : Maybe String
  main = goal >>= λ goal → return $ showList showAns (filterWithVars (solveToDepth 10 rules goal))
    where
      open RawMonad Maybe.monad
