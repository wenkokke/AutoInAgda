\section{Extensible proof search}
\label{sec:extensible}

As we promised in the previous section, we will now explore several
variations and extensions to the |auto| tactic described above.


\subsection*{Custom search strategies}

The simplest change we can make is to abstract over the search
strategy used by the |auto| function. In the interest of readability
we will create a simple alias for the types of search strategies.
\review{Briefly describe what the returned list represents (e.g. a list of goals to search for, in left-to-right order?).}
\begin{code}
  Strategy = (depth : ℕ) → SearchTree A → List A
\end{code}
The changed type of the |auto| function now becomes.
\begin{code}
  auto : Strategy → ℕ → HintDB → AgTerm → AgTerm
\end{code}
This will allow us to choose whether to pass in |dfs|, breadth-first
search or even a custom user-provided search strategy.


\subsection*{Custom hint databases}

Alternatively, we have developed a variant of the |auto| tactic
described in the paper that allows users to define their own type of
hint database, provided they can implement the following interface:
\begin{code}
      HintDB    : Set
      Hint      : ℕ → Set
      getHints  : HintDB → Hints
      getRule   : Hint k → Rule k
      getTr     : Hint k → (HintDB → HintDB)
\end{code}
Besides the obvious types for hints and rules, we allow hint databases
to evolve during the proof search. The user-defined |getTr| function
describes a transformation that may modify the hint database after a
certain hint has been applied.

Using this interface, we can implement alternative hint databases. For
instance, we could implement a `linear' proof search function that
removes a rule from the hint database after it has been
applied. Alternatively, we may want to assign priorities to our
hints. To illustrate one possible application of this interface, we
will describe a hint database implementation that limits the usage of
certain rules. Before we do so, however, we need to introduce a
motivating example.

\subsection*{Example: limited usage of hints}

We start by defining the following sublist relation, taken from the
Agda tutorial~\citep{agda-tutorial}:
\begin{code}
  data _⊆_ : List A → List A → Set where
    stop : [] ⊆ []
    drop : xs ⊆ ys  →      xs ⊆ y ∷ ys
    keep : xs ⊆ ys  → x ∷  xs ⊆ x ∷ ys
\end{code}
It is easy to show that the sublist relation is both reflexive and
transitive.

Using these rules, we can build up a small hint database to generate
proofs using the sublist relation.
\review{What are refl and trans? (Certainly not refl and trans for PropositionalEquality.)}
\begin{code}
  hintdb  : HintDB
  hintdb  = ε << quote drop << quote keep << quote refl << quote trans
\end{code}
Our |auto| tactic quickly finds a proof for the following lemma:
\begin{code}
  lemma₁  : ws ⊆ 1 ∷ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆ 1 ∷ 2 ∷ zs
  lemma₁  = tactic (auto dfs 10 hintdb)
\end{code}
The following lemma, however, is false.
\begin{code}
  lemma₂  : ws ⊆ 1 ∷ xs → xs ⊆ ys → ys ⊆ zs → ws ⊆ 2 ∷ zs
  lemma₂  = tactic (auto dfs 10 hintdb)
\end{code}
Indeed, this example does not type check and our tactic reports that
the search space is exhausted.  As noted by \citet{chlipala} when
examining tactics in Coq, |auto| will nonetheless spend a considerable
amount of time trying to construct a proof. As the |trans| rule is
always applicable, the proof search will construct the full search
tree up to the search depth -- resulting in an exponental running time.

We will use a variation of the |auto| tactic to address this
problem. Upon constructing the new hint database, users may assign
limits to the number of times certain hints may be used. By limiting the
usage of transitivity, our tactic will fail quicker.

To begin with, we choose the representation of our hints: a pair of a
rule and a `count' that describes how often the rule may still be
applied:
\begin{code}
  record Hint (k : ℕ) : Set where
    field
      rule   : Rule k
      count  : Count
\end{code}
These |count| values will either be a natural number (with a number |n|
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
We now revisit our original hint database and limit the number
of times transitivity may be applied:
\begin{code}
  hintdb  : HintDB
  hintdb  = ε  <<       quote drop
               <<       quote keep
               <<       quote refl
               <<[ 2 ]  quote trans
\end{code}
If we were to search for a proof of |lemma₂| now, our proof search
fails sooner. \emph{A fortiori}, if we use this restricted database
when searching for a proof of |lemma₁|, the |auto| function succeeds
sooner, as we have greatly reduced the search space. Of course, there
are plenty of lemmas that require more than two applications of
transitivity. The key insight, however, is that users now have control
over these issues -- something which is not even possible in current
implementations of |auto| in Coq.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
