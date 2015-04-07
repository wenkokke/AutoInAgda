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
terms
\begin{code}
data PsTerm (n : ℕ) : Set where
  var  : Fin n → PsTerm n
  con  : TermName → List (PsTerm n) → PsTerm n
\end{code}
We will use the name |PsTerm| to stand for \emph{proof search term} to
differentiate them from the terms from Agda's \emph{reflection}
mechanism, |AgTerm|.  In addition to variables, represented by the
finite type |Fin n|, we will allow first-order constants encoded as a
name with a list of arguments.

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


\subsection*{Inference rules}
\label{subsec:rules}

The hints in the hint database will form \emph{inference rules} that
we may use to prove a goal term. We represent such rules as records
containing a rule name, a list of terms for its premises, and a term
for its conclusion:
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
used in the rule. Note that the number of variables in the
premises and the conclusion is the same.

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

Before we can implement some form of proof search, we need to define a pair of
auxiliary functions. During proof resolution, we will work
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

Our proof search procedure is consists of two steps. First, we
coinductively construct a (potentially infinite) search space; next,
we will perform a bounded depth-first traversal of this space to find
a proof of our goal.

We will represent the search space as a (potentially) infinitely deep, but
finitely branching rose tree.
\begin{code}
  data SearchTree (A : Set) : Set where
    leaf  : A → SearchTree A
    node  : List (∞ (SearchTree A)) → SearchTree A
\end{code}
We will instantiate the type parameter |A| with a
type representing proof terms. These terms consist of applications of
rules, with a sub-proof for every premise.
\begin{code}
  data Proof : Set where
    con : (name : RuleName) (args : List Proof) → Proof
\end{code}
Unfortunately, during the proof search we will have to work with
\emph{partially complete} proof terms.

Such partial completed proofs are represented by the |PartialProof|
type. In contrast to the |Proof| data type, the |PartialProof| type
may contain variables, hence the type takes an additional number as
its argument:
\begin{code}
  PartialProof : ℕ → Set
  PartialProof m = ∃[ k ] Vec (PsTerm m) k × (Vec Proof k → Proof)
\end{code}
A value of type |PartialProof m| records three separate pieces of
information:
\begin{itemize}
\item a number |k|, representing the number of open subgoals;
\item a vector of length |k|, recording the subgoals that are still
  open;
\item a function that, given a vector of |k| proofs for each of the
  subgoals, will produce a complete proof of the original goal.
\end{itemize}
Next, we define the following auxiliary function to help construct partial
proof terms:
\begin{code}
  apply : (r : Rule n) → Vec Proof (arity r + k) → Vec Proof (suc k)
  apply r xs = new ∷ rest
    where
      new   = con (name r) (toList (take (arity r) xs))
      rest  = drop (arity r) xs
\end{code}
Given a |Rule| and a list of proofs of subgoals, this |apply| function
takes the required sub-proofs from the vector, and creates a new proof
by applying the argument rule to these sub-proofs. The result then consists of
this new proof, together with any unused sub-proofs. This is essentially
the `unflattening' of a rose tree.

We can now finally return to our proof search algorithm. The
|solveAcc| function forms the heart of the search procedure. Given a
hint database and the current partially complete proof, it produces a
|SearchTree| containing completed proofs. Note that while we will give
a complete definition for hint databases in
Section~\ref{sec:extensible}, for the moment, we will treat |HintDB|
as a list of |Rule|s.
\begin{code}
  solveAcc : HintDB -> PartialProof (δ + m) → SearchTree Proof
  solveAcc  rules  (0      ,      []  , p)  = leaf (p [])
  solveAcc  rules  (suc k  , g ∷  gs  , p)  = node (map step rules)
\end{code}
If there are no remaining subgoals, i.e., the list in the second
component of the |PartialProof| is empty, the search is finished. We
construct a proof |p []|, and wrap this in the |leaf| constructor of
the |SearchTree|. If we still have open subgoals, we have more work to
do. In that case, we will try to apply every rule in our hint database
to resolve this open goal---our rose tree has as many branches as
there are hints in the hint database. The real work is done by the
|step| function, locally defined in a where clause, that given the
rule to apply, computes the remainder of the |SearchTree|.

Before giving the definition of the |step| function, we will try to
provide some intuition. Given a rule, the |step| function will try to
unify its conclusion with the current subgoal |g|. When this succeeds,
the premises of the rule are added to the list of open subgoals. When
this fails, we return a |node| with no children, indicating that
applying this rule can never prove our current goal.

Carefully dealing with variables, however, introduces some
complication, as the code for the |step| function illustrates:
\begin{code}
step : ∃[ δ ] (Rule δ) → ∞ (SearchTree Proof)
step (δ , r)
     with unify (inject δ g) (raise m (conclusion r))
...  | nothing         = ♯ node []
...  | just (n , mgu)  = ♯ solveAcc prf
  where
  prf : PartialProof n
  prf = arity r + k , gs′ , (p ∘ apply r)
    where
    gs′ : Vec (Goal n) (arity r + k)
    gs′ = map (apply mgu) (raise m (fromList (premises r)) ++ inject δ gs)
\end{code}
The argument rule may have a number of free variables of its own. As a result,
all goals have to be injected into a larger domain which includes all
current variables \emph{and} the new rule's variables. The rule's
premises and conclusion are then also raised into this larger domain, 
to guarantee freshness of the rule variables.

The definition of the |step| function attempts to |unify| the current
subgoal |g| and conclusion of the rule |r|. If this fails, we can
return |node []| immediately. If this succeeds, however, we build up a
new partial proof, |prf|. This new partial proof, once again, consists of three parts:
\begin{itemize}
\item the number of open subgoals is incremented by |arity r|, i.e., the
  number of premises of the rule |r|.
\item the vector of open subgeals |gs| is extended with the premises
  of |r|, after weakening the variables of appropriately.
\item the function producing the final |Proof| object will, given the
  proofs of the premises of |r|, call |apply r| to create the desired
  |con| node in the final proof object.
\end{itemize}

The only remaining step, is to kick-off our proof search algorithm
with a partial proof, consisting of a open subgoal:
\begin{code}
  solve : (goal : PsTerm m) → HintDB → SearchTree Proof
  solve g rules = solveAcc (1 , g ∷ [] , head)
\end{code}

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
