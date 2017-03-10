open import Auto.Core
open import Data.List    using (_∷_; []; length)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Reflection   using (Term; Name; lam; visible; abs; TC; returnTC; bindTC)

module Auto.Extensible (instHintDB : IsHintDB) where


open IsHintDB     instHintDB public
open PsExtensible instHintDB public
open Auto.Core               public using (dfs; bfs; Exception; throw; searchSpaceExhausted; unsupportedSyntax)


auto : Strategy → ℕ → HintDB → Term → TC Term
auto search depth db type
  with agda2goal×premises type
... | inj₁ msg = returnTC (quoteError msg)
... | inj₂ ((n , g) , args)
  with search (suc depth) (solve g (fromRules args ∙ db))
... | []      = returnTC (quoteError searchSpaceExhausted)
... | (p ∷ _) = bindTC (reify p) (λ rp → returnTC (intros rp))
  where
    intros : Term → Term
    intros = introsAcc (length args)
      where
        introsAcc : ℕ → Term → Term
        introsAcc  zero   t = t
        introsAcc (suc k) t = lam visible (abs "TODO" (introsAcc k t))



infixl 5 _<<_

_<<_ : HintDB → Name → TC HintDB
db << n = bindTC (name2rule n) (λ
  {(inj₁ msg) → returnTC db
  ; (inj₂ (k , r)) → returnTC (db ∙ return r)})
-- db << n with (name2rule n)
-- db << n | inj₁ msg     = db
-- db << n | inj₂ (k , r) = db ∙ return r
