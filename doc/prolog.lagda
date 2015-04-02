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
In addition to variables, represented by the finite type |Fin n|, we
will allow first-order constants encoded as a name with a list of
arguments.

For instance, if we choose to instantiate |TermName| with the following
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
AddOne = con Add (var (# 0) ∷ One ∷ [])
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
compute a substitution---the most general unifier. Substitutions are
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

    arity : ℕ
    arity = length premises
\end{code}
Once again the data-type is quantified over the number of variables
used in the rule. Note that the variables are shared between the
premises and the conclusion.

Using our newly defined |Rule| type we can give a simple definition of
addition. In Prolog, this would be written as follows.
\begin{verbatim}
  add(0, X, X).
  add(suc(X), Y, suc(Z)) :- add(X, Y, Z).
\end{verbatim}
Unfortunately, the named equivalents in our Agda implementation given
in Figure~\ref{fig:rules} are a bit more verbose. Note that we have,
for the sake of this example, instantiated the |RuleName| and
|TermName| to |String| and |Arith| respectively.
\begin{figure}
  \centering
  \normalsize
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
  \caption{Agda representation of example rules}
  \label{fig:rules}
\end{figure}


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
On the surface, the |inject| function appears to be the identity. When you
make all the implicit arguments explicit, however, you will see that
it sends the |zero| constructor in |Fin m| to the |zero| constructor
of type |Fin (m + n)|. Hence, the |inject| function maps |Fin m| into the
\emph{first} |m| elements of the type |Fin (m + n)|. Dually, the
|raise| function maps |Fin n| into the \emph{last} |n| elements of the
type |Fin (m + n)| by repeatedly applying the |suc| constructor.

We can use |inject| and |raise| to define similar functions
that work on our |Rule| and |PsTerm| data types, by mapping them over
all the variables that they contain.


\subsection*{Constructing the search tree}
\label{subsec:searchtrees}

\todo{Wouter: reread, refactor and rewrite}

Our search tree is simply a (potentially) infinitely deep, but
finitely branching rose tree.
\begin{code}
  data SearchTree (A : Set) : Set where
    leaf  : A → SearchTree A
    node  : List (∞ (SearchTree A)) → SearchTree A
\end{code}
For our purposes, the type parameter |A| will be instantiated with a
type representing proof terms: a type which consists of applications of
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

\item Last, we recursively apply step~\ref{step:recurse} until we have
  emptied the list of sub-goals---which may never happen. When we do
  manage to resolve all sub-goals, we can return a complete proof term.
\end{enumerate}

Partial proofs are represented by the |Proof′| type, which is a pair
containing our list of sub-goals (of length |k|) combined with a
function from |k| proof terms to a proof term.
\begin{code}
  Proof′ : ℕ → Set
  Proof′ m = ∃[ k ] Vec (Goal m) k × (Vec Proof k → Proof)
\end{code}
\review{I think the "Goal" type should be "PsTerm" now.}
\pepijn{Should we reintroduce that alias, or should we replace all
  occurrences of Goal by PsTerm? I'm in favor of the first.}
This means that the initial partial proof for a goal |g| is
represented as the triple |(1 , g ∷ [] , head)|.

In order to simplify working with these partial proof terms, we define
a smart constructor for proof terms based on vectors of proofs. More
specifically, |con′| will, given a rule |r| and a vector of proof
terms, take |arity r| proofs off of the proof vector, apply the proof
constructor |con|, and cons the resulting term back into the proof
vector.
\review{the description of con' can't be parsed by me}
\begin{code}
  con′ : (r : Rule n) → Vec Proof (arity r + k) → Vec Proof (suc k)
  con′ r xs = new ∷ rest
    where
      new   = con (name r) (toList (take (arity r) xs))
      rest  = drop (arity r) xs
\end{code}
Finally, we define a function |solve| which builds up the tree, given
a hint database. This function is implemented with two accumulating
parameters, representing the current substitution and the current
partial proof, respectively.
These are initialized to the identity substitution and
a single proof obligation---as described above.
\review{One can only guess that HintDB will turn out to be a list of
  Rules eventually (because everything else does not make sense, given
  how "solve" passes its HintDB argument off to a "map" with "step :
  Rule -> ..." as the higher-order argument). I found it confusing
  that this connection was not made explicit then and there}
\begin{code}
  solve : Goal m → HintDB → SearchTree Proof
  solve g rules = solveAcc (just (m , nil)) (1 , g ∷ [] , head)
\end{code}
The actual work is done by the |solveAcc| function, that distinguishes
three important cases: if unification is impossible, and therefore the
current substitution |nothing|, we fail; if the partial proof is
complete, i.e. has no more holes, we can stop the search and construct
a |leaf|; otherwise, we continue the proof search by constructing a
node with one child for every possible node, by applying the
function |step|.
\begin{code}
  solveAcc : Maybe (∃[ n ] Subst (δ + m) n) → Proof′ (δ + m)
    → SearchTree Proof
  solveAcc  nothing         _                     = node [] -- fail
  solveAcc  (just (n , s))  (0 , [] , p)          = leaf (p [])
  solveAcc  (just (n , s))  (suc k , g ∷ gs , p)  = node (map step rules)
\end{code}
This |step| function is defined in Figure~\ref{fig:step}. It may seem
daunting, but what it does is relatively simple.\footnote{ Note that
  it is defined within a where clause of |solveAcc| and therefore has
  access to all its variables.  } First, it is given a rule which it
tries to apply. This rule may have a number of free variables of its
own. As a result, all terms---the rule's premises and conclusion, the
current goals, the current substitution---have to be injected into a
larger domain which includes all the current variables \emph{and} the
new rule's variables. This alone accounts for most of the code in the
where clauses.  Second, now that the terms are compatible, we attempt
to find a most general unifier (|mgu|) for the current goal and the
rule's conclusion. Note that if this fails, |unifyAcc| will return
|nothing| and cause |solveAcc| to fail on the next recursive call.
Finally, we build up a new partial proof, updating the previous one
with a new constructor for the given rule.  With all these values in
hand, we recursively call |solveAcc| to (lazily) generate the rest of
the search tree.

\begin{figure}
  \centering\normalsize
\begin{code}
  step : ∃[ δ′ ] Rule δ′ → ∞ (SearchTree Proof)
  step (δ′ , r) = ♯ solveAcc mgu prf
    where
      v : ℕ
      v = δ′ + δ + m
      prf : Proof′ v
      prf = arity r + k , prm′ ++ gs′ , p′
        where
          gs′   : Vec (Goal v) k
          gs′   = inject δ′ gs
          prm′  : Vec (Goal v) (arity r)
          prm′  = map (raise (δ + m)) (fromList (premises r))
          p′    : Vec Proof (arity r + k) → Proof
          p′    = p ∘ con′ r

      mgu : Maybe (∃[ n ] (Subst v n))
      mgu = unifyAcc g′ cnc′ s′
        where
          g′    : PsTerm v
          g′    = inject δ′ g
          cnc′  : PsTerm v
          cnc′  = raise (δ + m) (conclusion r)
          s′    : ∃[ n ] Subst v n
          s′    = n + δ′ , injectSubst δ′ s
\end{code}
  \caption{The |step| function}
  \label{fig:step}
\end{figure}

\subsection*{Searching for proofs}

After all this construction, we are left with a simple tree structure,
which we can traverse in search of solutions. For instance, we can
define a bounded depth-first traversal.
\begin{code}
  dfs : (depth : ℕ) → SearchTree A → List A
  dfs    zero       _         = []
  dfs (  suc k)  (  leaf x)   = return x
  dfs (  suc k)  (  node xs)  = concatMap (λ x → dfs k (♭ x)) xs
\end{code}
It is fairly straightforward to define other traversal strategies,
such as a breadth-first search.  Similarly, we could define a function
which traverses the search tree aided by some heuristic. We will
explore further variations on search strategies in
Section~\ref{sec:extensible}.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
