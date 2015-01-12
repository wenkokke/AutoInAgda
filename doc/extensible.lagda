\section{Extensible proof search}
\label{sec:extensible}

As we promised in the previous section, we will now investigate
possibilities and applications for a more extensible |auto|.


\subsection*{Custom search strategies}

The simplest change we can make is to abstract over the search
strategy used by the |auto| function. In the interest of readability
we will create a simple alias for the types of search strategies.
\begin{code}
  Strategy = (depth : ℕ) → SearchTree A → List A
\end{code}
The changed type of the |auto| function now becomes.
\begin{code}
  auto : Strategy → ℕ → HintDB → AgTerm → AgTerm
\end{code}
This will allow us to choose whether to pass in |dfs|, |bfs| or even a
custom user-provided search strategy.


\subsection*{Custom hint databases}

A more radical change we could make to our |auto| function is the
following: we allow the user to submit any custom type for hint
databases, as long as it implements a basic interface.
\begin{code}
  record IsHintDB : Set₁ where
    field
      HintDB    : Set
      Hint      : ℕ → Set
      getHints  : HintDB → Hints
      getRule   : Hint k → Rule k
      getTr     : Hint k → (HintDB → HintDB)
\end{code}
In addition to this, we allow hint databases to evolve during the
proof search, by supplying a transformation function, through |getTr|,
which computes a new hint database based on the selected hint.

Using this interface, we can easily script all kinds of proof
search. For instance, linear search could easily be implemented by
setting the transition function to |delete| the selected rule from the
hint database.


\subsection*{Example: limited usage of hints}

To illustrate the custom hint databases introduced above, introduce a
new example: the sublist relation.
\begin{code}
  data _⊆_ : List A → List A → Set where
    stop : [] ⊆ []
    drop : xs ⊆ ys  →      xs ⊆ y ∷ ys
    keep : xs ⊆ ys  → x ∷  xs ⊆ x ∷ ys
\end{code}
It is easy to show that the sublist relation is both reflexive and
transitive.

Using these rules, we can build up a small hint database to reason
about the sublist relation.
\begin{code}
  hintdb  : HintDB
  hintdb  = ε << quote drop << quote keep << quote refl << quote trans
\end{code}
We can use this hint database to easily prove lemmas about the sublist
relation. For instance, |auto| quickly finds a proof for the following
lemma.
\begin{code}
  lemma₁  : ws ⊆ 1 ∷ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆ 1 ∷ 2 ∷ zs
  lemma₁  = tactic (auto dfs 7 hintdb)
\end{code}
The following lemma is false. However, as noted by \citet{chlipala}
when examining tactics in Coq, |auto| will spend a lot of time
searching for proofs of it.
\begin{code}
  lemma₂  : ws ⊆ 1 ∷ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆ 2 ∷ zs
  lemma₂  = tactic (auto dfs 10 hintdb)
\end{code}
The reason is that the |trans| rule is always applicable. This will
cause the proof search to construct the full search tree up to the
search depth---resulting in an exponental running time.


We will use our extensible |auto| tactic to implement a quick fix for
this problem. We will implement a 'counting' hint database; one in
which each hint will be associated with a usage count, representing
the number of times the hint can still be applied.

Starting out, we will choose the representation of our hints: a pair
of a rule and a 'count'.
\begin{code}
  record Hint (k : ℕ) : Set where
    field
      rule   : Rule k
      count  : Count
\end{code}
These 'count' values will either be a natural number (with a number |n|
meaning that the rule can still be used |n| times) or |⊤| (meaning
that the usage of the rule is unrestricted).
\begin{code}
  Count : Set
  Count = ℕ ⊎ ⊤
\end{code}
For this to work we will define a decrementing function, |decrCount|,
which will decrement a count: if we are given a natural number, we
return its predecessor; if we are given top, we return top; and
finally, if the count is |0| or |1| then the rule should be removed,
and we will return |nothing|.
\begin{code}
  decrCount : Count → Maybe Count
  decrCount (inj₁ 0)   = nothing
  decrCount (inj₁ 1)   = nothing
  decrCount (inj₁ x)   = just (inj₁ (pred x))
  decrCount (inj₂ tt)  = just (inj₂ tt)
\end{code}
Given a hint |h|, the transition function will now simply find the
position of |h| in the hint database and decrement the hint's count,
removing it from the database if necessary.

The default insertion function (|_<<_|) will still assume that a rule
can be applied endlessly. However, we will define a new insertion
function which will allow the user to specify how often a rule should
be allowed in a derivation.
\begin{code}
  _<<[_]_ : HintDB → ℕ → Name → HintDB
  db <<[ 0 ] _ = db
  db <<[ x ] n with (name2rule n)
  db <<[ x ] n | inj₁ msg     = db
  db <<[ x ] n | inj₂ (k , r) = db ++ [ k , record { rule = r , count = inj₁ x } ]
\end{code}
Imagine we, had constructed our hint database as follows, using our
new counting databases.
\begin{code}
  hintdb  : HintDB
  hintdb  = ε  <<       quote drop
               <<       quote keep
               <<       quote refl
               <<[ 2 ]  quote trans
\end{code}
If we were to search for a proof of |lemma₂| now, our proof search
terminate much sooner, as it would run out of applicable rules. And
even better! If we use this restricted database when searching for a
proof of |lemma₁|, the |auto| function terminates much sooner, as we
have greatly reduced the number of possible proofs to search through!

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
