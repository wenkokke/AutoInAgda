open import Auto.Core 
open import Data.List    using (_∷_; []; length)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Reflection   using (Term; Name; lam; visible)

module Auto.Extensible (instHintDB : IsHintDB) where


open IsHintDB     instHintDB public
open PsExtensible instHintDB public
open Auto.Core               public using (dfs; bfs; Exception; throw; searchSpaceExhausted; unsupportedSyntax)


auto : Strategy → ℕ → HintDB → Term → Term
auto search depth db type
  with agda2goal×premises type
... | inj₁ msg = quoteError msg
... | inj₂ ((n , g) , args)
  with search (suc depth) (solve g (fromRules args ∙ db))
... | []      = quoteError searchSpaceExhausted
... | (p ∷ _) = intros (reify p)
  where
    intros : Term → Term
    intros = introsAcc (length args)
      where
        introsAcc : ℕ → Term → Term
        introsAcc  zero   t = t
        introsAcc (suc k) t = lam visible (introsAcc k t)



infixl 5 _<<_

_<<_ : HintDB → Name → HintDB
db << n with (name2rule n)
db << n | inj₁ msg     = db
db << n | inj₂ (k , r) = db ∙ return r
