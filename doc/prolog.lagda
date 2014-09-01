\section{Proof search in Agda}
\label{sec:prolog}

The following section describes our implementation of proof search
à la Prolog in Agda. This implementation abstracts over two data types
for names---one for inference rules and term constructors. These data
types will be referred to as |RuleName| and |TermName|, and will be
instantiated with types (with the same names) in
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
\subsection*{Constructing the search tree}
\subsection*{Searching for proofs}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
