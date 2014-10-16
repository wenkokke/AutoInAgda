\section{Proof search in Agda}
\label{sec:prolog}

The following section describes our implementation of proof search
à la Prolog in Agda. This implementation abstracts over two data types
for names---one for inference rules and one for term constructors.
These data types will be referred to as |RuleName| and |TermName|, and
will be instantiated with concrete types (with the same names) in
section~\ref{sec:reflection}.


\subsection*{Terms and unification}
\label{subsec:terms}

The heart of our proof search implementation is the structurally
recursive unification algorithm described by~\citet{unification}. Here
the type of terms is indexed by the number of variables a given term
may contain. Doing so enables the formulation of the unification
algorithm by structural induction on the number of free variables.
For this to work, we will use the following definition of
terms\footnote{
  We will use the name |PsTerm| to stand for \emph{proof search term}
  to differentiate them from Agda's \emph{reflection terms}, or |AgTerm|.
}:
\begin{code}
data PsTerm (n : ℕ) : Set where
  var  : Fin n → PsTerm n
  con  : TermName → List (PsTerm n) → PsTerm n
\end{code}
In addition to a restricted set of variables, we will allow
first-order constants encoded as a name with a list of
arguments.

For instance, if we choose to instantiate |PsName| with the following
|Arith| data type, we can encode numbers and simple arithmetic
expressions:
\begin{code}
data Arith : Set where
  Suc   : Arith
  Zero  : Arith
  Add   : Arith
\end{code}
The closed term corresponding to the number one could be written as follows:
\begin{code}
One : PsTerm 0
One = con Suc (con Zero [] ∷ [])
\end{code}
Similarly, we can use the |var| constructor to represent open terms,
such as |x + 1|. We use the prefix operator |#| to convert from
natural numbers to finite types:
\begin{code}
AddOne : PsTerm 1
AddOne = con Add (var (# 0) ∷ con One [] ∷ [])
\end{code}
Note that this representation of terms is untyped. There is no check
that enforces addition is provided precisely two arguments. Although
we could add further type information to this effect, this introduces
additional overhead without adding safety to the proof automation
presented in this paper. For the sake of simplicity, we have therefore
chosen to work with this untyped definition.

We shall refrain from further discussion of the unification algorithm itself.
Instead, we restrict ourselves to presenting the interface that we will use:
\begin{code}
  unify  : (t₁ t₂ : PsTerm m) → Maybe (∃[ n ] Subst m n)
\end{code}
The |unify| function takes two terms |t₁| and |t₂| and tries to
compute a sustitution---the most general unifier. Substitutions are
indexed by two natural numbers |m| and |n|. A substitution of type
|Subst m n| can be applied to a |PsTerm m| to produce a value of type
|PsTerm n|.
As unification may fail, the result is wrapped in the |Maybe| type. In
addition, since the number of variables in the terms resulting from
the unifying substitution is not known \emph{a priori}, this
number is existentially quantified over.
For the remainder of the paper, we will write |∃[ x ] B| to mean a
type |B| with occurrences of an existentially quantified variable |x|,
or |∃ (λ x → B)| in full.

Occasionally we will use a more general function |unifyAcc|, which
takes a substitution as an additional parameter. It applies this
substitution to |t₁| and |t₂| before attempting to unify.
\begin{code}
  unifyAcc  : (t₁ t₂ : PsTerm m)
            → ∃[ n ] Subst m n → Maybe (∃[ n ] Subst m n)
\end{code}


\subsection*{Inference rules}
\label{subsec:rules}

We encode inference rules as records containing a rule name, a list of
terms for its premises, and a term for its conclusion:
\begin{code}
  record Rule (n : ℕ) : Set where
    field
      name        : RuleName
      premises    : List (PsTerm n)
      conclusion  : PsTerm n
\end{code}
Once again the data-type is quantified over the number of variables
used in the rule. Note that the variables are shared between the
premises and the conclusion.

Using our newly defined |Rule| we can give a simple definition of
addition. In Prolog, this would be written as follows.
\begin{verbatim}
  add(0, X, X).
  add(suc(X), Y, suc(Z)) :- add(X, Y, Z).
\end{verbatim}
Unfortunately, the named equivalents in our Agda implementation are a
bit more verbose. Note that we have, for the sake of this example,
instantiated the |RuleName| and |TermName| to |String| and |Arith|
respectively.
\begin{code}
AddBase : Rule 1
AddBase = record {
  name        = "AddBase"
  conclusion  = con Add  (  con Zero []
                         ∷  var (# 0)
                         ∷  var (# 0)
                         ∷ [])
  premises    = []
  }
\end{code}%
\begin{code}
AddStep : Rule 3
AddStep = record {
  name        = "AddStep"
  conclusion  =  con Add  (  con Suc (var (# 0) ∷ [])
                          ∷  var (# 1)
                          ∷  con Suc (var (# 2) ∷ [])
                          ∷ [])
  premises    =  con Add  (  var (# 0)
                          ∷  var (# 1)
                          ∷  var (# 2)
                          ∷ [])
                 ∷ []
  }
\end{code}


\subsection*{Generalised injection and raising}
\label{subsec:injectandraise}

Before we can implement some form of proof search, we define a pair of
auxiliary functions. During proof resolution, we will need to work
with terms and rules containing a different number of variables. We
will use the following pair of functions, |inject| and |raise|, to
weaken bound variables, that is, map values of type |Fin n| to some
larger finite type.
\begin{code}
  inject : ∀ {m} n → Fin m → Fin (m + n)
  inject n  zero    = zero
  inject n (suc i)  = suc (inject n i)

  raise : ∀ m {n} → Fin n → Fin (m + n)
  raise  zero    i  = i
  raise (suc m)  i  = suc (raise m i)
\end{code}
We have tried to visualize the behaviour of |inject| and |raise|,
embedding |Fin 3| into |Fin (3 + 1)| in Figure~\ref{fig:fins}. On the
surface, the |inject| function appears to be the identity. When you
make all the implicit arguments explicit, however, you will see that
it sends the |zero| constructor in |Fin m| to the |zero| constructor
of type |Fin (m + n)|. Hence, the |inject| function maps |Fin m| into the
\emph{first} |m| elements of the type |Fin (m + n)|. Dually, the
|raise| function maps |Fin n| into the \emph{last} |n| elements of the
type |Fin (m + n)| by repeatedly applying the |suc| constructor.

\begin{figure}
  \centering
  \subfigure[]{ \label{fig:injFig}
    \begin{tikzpicture}[place/.style={circle,draw=darkgray!50,fill=gray!20,thick}]
       \node[place,label=left:1] (one3) {};
       \node[place,label=left:2] (two3) [below=of one3] {};
       \node[place,label=left:3] (three3) [below=of two3] {};

       \node[place,label=right:1] (one4) [right=of one3] {};
       \node[place,label=right:2] (two4) [below=of one4] {};
       \node[place,label=right:3] (three4) [below=of two4] {};
       \node[place,label=right:4] (four4) [below=of three4] {};

       \draw [->] (one3) to [thick, shorten <=1pt,>=stealth'] (one4);
       \draw [->] (two3) to [thick, shorten <=1pt,>=stealth']  (two4);
       \draw [->] (three3) to [thick, shorten <=1pt,>=stealth']  (three4);
    \end{tikzpicture}}
\hspace{7.5em}
  \subfigure[]{
  \begin{tikzpicture} [place/.style={circle,draw=darkgray!50,fill=gray!20,thick}]
       \node[place,label=left:1] (one3) {};
       \node[place,label=left:2] (two3) [below=of one3] {};
       \node[place,label=left:3] (three3) [below=of two3] {};

       \node[place,label=right:1] (one4) [right=of one3] {};
       \node[place,label=right:2] (two4) [below=of one4] {};
       \node[place,label=right:3] (three4) [below=of two4] {};
       \node[place,label=right:4] (four4) [below=of three4] {};

       \draw [->] (one3) to [thick, shorten <=1pt,>=stealth'] (two4);
       \draw [->] (two3) to [thick, shorten <=1pt,>=stealth']  (three4);
       \draw [->] (three3) to [thick, shorten <=1pt,>=stealth']  (four4);
  \end{tikzpicture}}

\vspace{4ex}
\caption{The graph of the |inject| function (a) and the |raise|
  function (b) embedding |Fin 3| in |Fin (3 + 1)|}
\label{fig:fins}
\end{figure}
We can use these |inject| and |raise| to define similar functions
that work on our |Rule| and |PsTerm| data types, by mapping them over
all the variables that they contain.


\subsection*{Constructing the search tree}
\label{subsec:searchtrees}

Our search tree is simply a potentially infinite rose tree.
\begin{code}
  data SearchTree (A : Set) : Set where
    leaf  : A → SearchTree A
    node  : List (∞ (SearchTree A)) → SearchTree A
\end{code}
For our purposes, the type parameter |A| will be instantiated with a
type representing proof terms: a type which exists of applications of
rules, with a sub-proof for every parameter.
\begin{code}
  data Proof : Set where
    con : (name : RuleName) (args : List Proof) → Proof
\end{code}
We construct our search trees as follows:
\begin{enumerate}
\item \label{step:base}
  We begin with a partial proof term which consists of a single hole,
  representing a proof obligation for our top-level goal. We represent
  this as a function from a single proof object to the resulting proof
  object.

\item \label{step:recurse}
  Next, for each rule |r| in our hint database, we attempt to unify
  the conclusion of |r| with the goal. If this succeeds, we add the
  premises of |r| to the list of sub-goals. In addition, we update the
  structure of the partial proof, instantiating the hole with our rule
  |r|, and creating new holes for the premises of |r|.

\item
  Last, we recursively apply step~\ref{step:recurse} until we have
  emptied the list of sub-goals---which may never happen. If this is
  the case, then we will provably also have a complete proof term,
  which we can return.
\end{enumerate}
A sample search-tree can be seen in figure~\ref{fig:searchtree}.

\begin{figure}[ht]
  \begin{tikzpicture}[thick, scale=0.8]
    \Tree [.{\ldots} {|isEven0|}
      [.{(|isEven+2| \, \ldots)}
        [.{(|isEven+2| \, |isEven0|)} ]
        [.{(|isEven+2| \, |isEven+2| \, {\vdots})} {\vdots} ]
        [.{\vdots} ]
      ]
      [.{(|even+| \, \ldots \, \ldots)} {\vdots} ]
    ]
  \end{tikzpicture}
  \caption{Sample search tree during construction.}
  \label{fig:searchtree}
\end{figure}

Partial proofs are represented by the |Proof′| type, which is a pair
containing our list of sub-goals (of length |k|) combined with a
function from |k| proof terms to a proof term.
\begin{code}
  Proof′ : ℕ → Set
  Proof′ m = ∃[ k ] Vec (Goal m) k × (Vec Proof k → Proof)
\end{code}
This means that the initial partial proof for a goal |g| is
represented as the triple |(1 , g ∷ [] , head)|.

In order to simplify working with these partial proof terms, we define
a smart constructor for proof terms based on vectors of proofs. More
specifically, |con′| will, given a rule |r| and a vector of proof
terms, take |arity r| proofs off of the proof vector apply the proof
constructor |con|, and cons the resulting term back into the proof
vector.
\begin{code}
  con′ : (r : Rule n) → Vec Proof (arity r + k) → Vec Proof (suc k)
  con′ r xs = new ∷ rest
    where
      new  = con (name r) (toList (take (arity r) xs))
      rest = drop (arity r) xs
\end{code}
Finally, we define a function |solve| which builds up the tree, given
a hint database. This function is implemented with two accumulating
parameters, representing the current substitution and the current
partial proof, respectively.
In the base case, these are instantiated to the empty substitution and
a single proof obligation---as described above.
\begin{code}
  solve : Goal m → HintDB → SearchTree Proof
  solve g rules = solveAcc (just (m , nil)) (1 , g ∷ [] , head)
\end{code}
In the recursive construction, there are three important cases: if
unification is impossible, and therefore the current substitution
|nothing|, we fail; if the partial proof is complete, i.e. has no more
holes, we can stop the search and construct a |leaf|; otherwise, we
continue the proof search by constructing a node with one child for
every possible node, by applying the stepping function.
\begin{code}
  solveAcc : Maybe (∃[ n ] Subst (δ + m) n)
           → Proof′ (δ + m) → SearchTree Proof
  solveAcc nothing _ = node [] -- fail
  solveAcc (just (n , s)) (0 , [] , p) = leaf (p [])
  solveAcc (just (n , s)) (suc k , g ∷ gs , p) = node (map step rules)
\end{code}
The stepping function itself looks daunting, but what it does is
relatively simple.\footnote{
  Note that it is defined within a where clause of |solveAcc| and
  therefore has access to all its variables.
}
First, it is given a rule to try and apply. Because this rule has a
number of free variables of its own, all terms---the rule's premises
and conclusion, the current goals, the current substitution---have to
be injected into a larger domain which includes all the current
variables \emph{and} the new rule's variables. This alone accounts for
most of the code in the where clauses.
Second, now that the terms are compatible, we attempt to find a most
general unifier (|mgu|) for the current goal and the rule's
conclusion. Note that if this fails, |unifyAcc| will return |nothing|
and cause |solveAcc| to fail on the next recursive call.
Finally, we build up a new partial proof, updating the previous one
with a new constructor for the given rule.
All these values in hand, we recursively call |solveAcc| to (lazily)
generate the rest of the search tree.
\begin{code}
  step : ∃[ δ′ ] Rule δ′ → ∞ (SearchTree Proof)
  step (δ′ , r) = ♯ solveAcc mgu prf
    where
      prf : Proof′ (δ′ + δ + m)
      prf = arity r + k , prm′ ++ gs′ , p′
        where
          gs′  : Vec (Goal (δ′ + δ + m)) k
          gs′  = inject δ′ gs
          prm′ : Vec (Goal (δ′ + δ + m)) (arity r)
          prm′ = map (raise (δ + m)) (fromList (premises r))
          p′   : Vec Proof (arity r + k) → Proof
          p′   = p ∘ con′ r

      mgu : Maybe (∃[ n ] (Subst (δ′ + δ + m) n))
      mgu = unifyAcc g′ cnc′ s′
        where
          g′   : PsTerm (δ′ + δ + m)
          g′   = inject δ′ g
          cnc′ : PsTerm (δ′ + δ + m)
          cnc′ = raise (δ + m) (conclusion r)
          s′   : ∃[ n ] Subst (δ′ + δ + m) n
          s′   = n + δ′ , injectSubst δ′ s
\end{code}
\todo{We should try to clean up this code a bit. Introducing a
  separate name for |δ′ + δ + m| would really help keep the type
  signatures manageable}

\subsection*{Searching for proofs}

After all this construction, we are left with a simple tree structure,
which we can traverse in search of solutions. For instance, we can
define a simple bounded depth-first traversal as follows:
\begin{code}
  dfs : (depth : ℕ) → SearchTree A → List A
  dfs zero     _          = []
  dfs (suc k)  fail       = []
  dfs (suc k)  (retn x)   = return x
  dfs (suc k)  (fork xs)  = concatMap (λ x → dfs k (♭ x)) xs
\end{code}
It is fairly straightforward to define other traversal strategies,
such as a breadth-first search, which traverses the search tree in
layers.
\begin{code}
  bfs : (depth : ℕ) → SearchTree A → List A
  bfs depth t = concat (Vec.toList (bfsAcc depth t))
    where
      merge : (xs ys : Vec (List A) k) → Vec (List A) k
      merge [] [] = []
      merge (x ∷ xs) (y ∷ ys) = (x ++ y) ∷ merge xs ys

      empty : Vec (List A) k
      empty {k = zero}  = []
      empty {k = suc k} = [] ∷ empty

      bfsAcc
        : (depth : ℕ) → SearchTree A → Vec (List A) depth
      bfsAcc  zero   _         = []
      bfsAcc (suc k) (leaf x)  = (x ∷ []) ∷ empty
      bfsAcc (suc k) (node xs) =
        [] ∷ foldr merge empty (map (λ x → bfsAcc k (♭ x)) xs)
\end{code}
Similarly, we could define a function which traverses the search tree
aided by several heuristics.



If we are willing to make further changes, we could also represent a
hint database as a list of \emph{pairs} of rules and functions of the
type |HintDB → HintDB|, such that after a rule |r| is selected in the
construction phase, it can update the hint database that is passed
down the tree.

This would make it relatively easy to implement, for instance, a
linear proof search, where every rule is applied at most once---we
would only have to pass in a function which deleted the selected rule
from the hint database.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
