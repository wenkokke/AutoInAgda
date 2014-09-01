\section{Proof search in Agda}
\label{sec:prolog}

The following section describes our implementation of proof search
à la Prolog in Agda. This implementation abstracts over two data types
for names---one for inference rules and one for term constructors.
These data types will be referred to as |RuleName| and |TermName|, and
will be instantiated with types (with the same names) in
section~\ref{sec:reflection}.


\subsection*{Terms and unification}

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

\begin{code}
  data SearchTree (A : Set) : Set where
    fail : SearchTree A
    retn : A → SearchTree A
    fork : List (∞ (SearchTree A)) → SearchTree A
\end{code}

\begin{code}
  data Proof : Set where
    con : (name : RuleName) (args : List Proof) → Proof
\end{code}

\begin{code}
  Proof′ : ℕ → Set
  Proof′ m = ∃[ k ] Vec (Goal m) k × (Vec Proof k → Proof)
\end{code}

\begin{code}
  con′ : (r : Rule n) → Vec Proof (arity r + k) → Vec Proof (suc k)
  con′ r xs = con (name r) (toList $ take (arity r) xs) ∷ drop (arity r) xs
    where
      prf :
\end{code}

\begin{code}
  solve : Goal m → HintDB → SearchTree Proof
  solve g rules = solveAcc (just (m , nil)) (1 , g ∷ [] , head)
\end{code}

\begin{code}
  solveAcc : Maybe (∃[ n ] Subst (δ + m) n)
           → Proof′ (δ + m) → SearchTree Proof
  solveAcc nothing _ = fail
  solveAcc (just (n , s)) (0 , [] , p) = retn (p [])
  solveAcc (just (n , s)) (suc k , g ∷ gs , p) = fork (map step rules)
\end{code}

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



\subsection*{Searching for proofs}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
