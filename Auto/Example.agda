open import Auto
open import Function using (_$_; _∘_)
open import Category.Functor
open import Category.Monad
open import Data.Bin as Bin using (Bin; 0#)
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; _∷_; []; [_]; concat; concatMap; fromMaybe)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (∃; _,_)
open import Data.String using (String)

module Auto.Example where

private
open RawMonad {{...}}
MonadMaybe = Maybe.monad

-- At the moment, the following rule does not yet compile (i.e. it
-- produces `nothing`) as the `Fin` datatype is indexed by a variable,
-- and first-order datatypes are not yet supported.

fin2nat : Maybe (∃ Rule)
fin2nat = name2rule (quote Fin.toℕ)

fin2nat′ : Maybe (List (∃ Rule))
fin2nat′ = name2rule′ (quote Fin.toℕ)

-- However, the `show` function for ℕ is supported, as it a simple
-- propositional type.

nat2str : Maybe (∃ Rule)
nat2str = name2rule (quote showℕ)

nat2str′ : Maybe (List (∃ Rule))
nat2str′ = name2rule′ (quote showℕ)

-- The same holds for the successor function on ℕ. The difference is that
-- the `suc` function is a constructor.

bin2nat : Maybe (∃ Rule)
bin2nat = name2rule (quote Bin.toℕ)

bin2nat′ : Maybe (List (∃ Rule))
bin2nat′ = name2rule′ (quote Bin.toℕ)

-- Just to check if the general example would work, we can try to add a binary
-- number atom to the ruleset.

bin nat : Maybe (∃ Rule)
bin = name2rule (quote 0#)
nat = name2rule (quote zero)

bin′ nat′ : Maybe (List (∃ Rule))
bin′ = name2rule′ (quote 0#)
nat′ = name2rule′ (quote zero)

-- A general note; the current type for the conversion functions `name2rule`
-- and `term2term` is rather short-sighted, as they allow the function to determine
-- its own number of arguments. Instead, this should be left existentially quantified
-- as a rule obviously needs to be able to determine its own number of arguments.
-- For the time being, we'll rely on a number of helper functions to construct the ruleset
-- out of these "potential" rules.

catMaybes : ∀ {α} {A : Set α} → List (Maybe A) → List A
catMaybes = concatMap fromMaybe

-- We can construct a ruleset out of all the rules that compile (though I
-- should probably look into a method for emitting a warning when a rule
-- does not produce a valid rule).

apply compose : Maybe (∃ Rule)
apply   = just ( 2 , Apply )
compose = just ( 3 , Compose )

rules : Rules
rules = catMaybes (apply ∷ nat2str ∷ nat ∷ [])

compose′ : Maybe (List (∃ Rule))
compose′ = just [ 3 , Compose ]

rules′ : Rules
rules′ = concat (catMaybes (bin′ ∷ []))

-- Finally we can see if Agda knows how to compute a term of type `Bin → String`,
-- using the set of rules that we have given it.

goal : Maybe (PTerm 0)
goal = term2term (quoteTerm Bin)

-- I'm reasonably sure that the search-depth parameter is quite unintuitive, as
-- what it's actually doing is limiting the depth of a *binary* search tree, where
-- every branch counts as going one deeper as well.
-- Aside from that, we don't find an answer when using only a single rule, that has
-- no premises.

main : Maybe String
main = showList showAns ∘ filterWithVars ∘ solveToDepth 2 rules′ <$> goal
