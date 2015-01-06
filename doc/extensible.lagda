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

To illustrate the custom hint databases introduced above, we will use
them to implement a 'counting' hint database; one in which each hint
will be associated with a usage count, representing the number of
times the hint can still be applied. 
For this we will represent hints as the pair of a rule and a 'count'.
\begin{code}
  record Hint (k : ℕ) : Set where
    field
      rule   : Rule k
      count  : Count
\end{code}
These 'count' values are either a natural number (with a number |n|
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

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
