\section{Extensible proof search}
\label{sec:extensible}

As we promised in the previous section, we will now explore several
variations and extensions to the |auto| tactic described above.


\subsection*{Custom search strategies}

The simplest change we can make is to abstract over the search
strategy used by the |auto| function. In the interest of readability
we will create a simple alias for the types of search strategies.
A |Strategy| represents a function which searches a |SearchTree| up to
|depth|, and returns a list of the leaves (or |Proof|s) found in the
|SearchTree| in an order which is dependent on the search strategy.
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

In addition, we have developed a variant of the |auto| tactic
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

Using this interface, we can implement many variations on proof
search. For instance, we could implement a `linear' proof search
function that removes a rule from the hint database after it has been
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
transitive---and using these simple proofs, we can build up a small
hint database to search for proofs on the sublist relation.
\begin{code}
  hintdb  : HintDB
  hintdb  = ε << quote drop << quote keep << quote ⊆-refl << quote ⊆-trans
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
always applicable, the proof search will construct a search tree up to
the full search depth---resulting in an exponental running time.

We will use a variation of the |auto| tactic to address this
problem. Upon constructing the new hint database, users may assign
limits to the number of times certain hints may be used. By limiting the
usage of transitivity, our tactic will fail more quickly.

To begin with, we choose the representation of our hints: a pair of a
rule and a `counter' that records how often the rule may still be
applied:
\begin{code}
  record Hint (k : ℕ) : Set where
    field
      rule     : Rule k
      counter  : Counter
\end{code}
These |counter| values will either be a natural number |n|,
representing that the rule can still be used at most |n|
times; or |⊤|, when the usage of the rule is unrestricted.
\begin{code}
  Counter : Set
  Counter = ℕ ⊎ ⊤
\end{code}
Next, we define a decrementing function, |decrCounter|, that returns
|nothing| when a rule can no longer be applied:
\begin{code}
  decrCounter : Counter → Maybe Counter
  decrCounter (inj₁ 0)   = nothing
  decrCounter (inj₁ 1)   = nothing
  decrCounter (inj₁ x)   = just (inj₁ (pred x))
  decrCounter (inj₂ tt)  = just (inj₂ tt)
\end{code}
Given a hint |h|, the transition function will now simply find the
position of |h| in the hint database and decrement the hint's counter,
removing it from the database if necessary.

We can redefine the default insertion function (|_<<_|) to allow
unrestricted usage of a rule. However, we will define a new insertion
function which will allow the user to limit the usage of a rule during proof search:
\begin{code}
  _<<[_]_ : HintDB → ℕ → Name → HintDB
  db <<[ 0 ] _ = db
  db <<[ x ] n with (name2rule n)
  db <<[ x ] n | inj₁ msg     = db
  db <<[ x ] n | inj₂ (k , r) = db ++ [ k , record { rule = r , counter = inj₁ x } ]
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
