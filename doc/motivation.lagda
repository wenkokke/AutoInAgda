\section{Motivation}
\label{sec:motivation}

Before describing the \emph{implementation} of our library, we will
provide a brief introduction to Agda's reflection mechanism and
illustrate how the proof automation described in this paper may be
used.

\subsection*{Reflection in Agda}

Agda has a \emph{reflection} mechanism\footnote{Note that Agda's
  reflection mechanism should not be confused with `proof by
  reflection' -- the technique of writing a verified decision
  procedure for some class of problems.} for compile time
metaprogramming in the style of Lisp~\citep{lisp-macros},
MetaML~\citep{metaml}, and Template
Haskell~\citep{template-haskell}. This reflection mechanism makes it
possible to convert a program fragment into its corresponding abstract
syntax tree and vice versa. We will introduce Agda's reflection
mechanism here with several short examples, based on the explanation
in previous work~\citep{van-der-walt}. A more complete overview can be
found in the Agda release notes~\citep{agda-relnotes-228} and Van der
Walt's thesis~\citep{vdWalt:Thesis:2012}.

The type |Term : Set| is the central type provided by the reflection mechanism.
It defines an abstract syntax tree for Agda terms. There are several
language constructs for quoting and unquoting program fragments. The simplest
example of the reflection mechanism is the quotation of a single
term. In the definition of |idTerm| below, we quote the identity
function on Boolean values.
\begin{code}
  idTerm : Term
  idTerm = quoteTerm (λ (x : Bool) → x)
\end{code}
When evaluated, the |idTerm| yields the following value:
\begin{code}
  lam visible (var 0 [])
\end{code}
On the outermost level, the |lam| constructor produces a lambda
abstraction. It has a single argument that is passed explicitly (as
opposed to Agda's implicit arguments). The body of the lambda consists
of the variable identified by the De Bruijn index 0, applied to an
empty list of arguments.

The |quote| language construct allows users to access the internal
representation of an identifier, a value of a built-in type
|Name|. Users can subsequently request the type or definition of such
names.
\review{I don't see how quote is more general than quoteTerm. If
  anything it seems like it would be the other way around.}

\review{Mention that unquoted terms have to be type checked.}

Dual to quotation, the |unquote| mechanism allows users to splice in a
|Term|, replacing it with its concrete syntax. For example, we could
give a convoluted definition of the |K| combinator as follows:
\begin{code}
  const : ∀ {A B} → A  → B → A
  const = unquote (lam visible (lam visible (var 1 [])))
\end{code}
The language construct |unquote| is followed by a value of type
|Term|. In this example, we manually construct a |Term| representing
the |K| combinator and splice it in the definition of |const|.

The final piece of the reflection mechanism that we will use is the
|quoteGoal| construct. The usage of |quoteGoal| is best illustrated
with an example:
\begin{code}
  goalInHole : ℕ
  goalInHole = quoteGoal g in hole
\end{code}
In this example, the construct |quoteGoal g| binds the |Term|
representing the \emph{type} of the current goal, |ℕ|, to the variable
|g|. When completing this definition by filling in the hole labeled
|0|, we may now refer to the variable |g|. This variable is bound to
|def ℕ []|, the |Term| representing the type |ℕ|.

\subsection*{Using proof automation}

To illustrate the usage of our proof automation, we begin by defining a
predicate |Even| on natural numbers as follows:

\begin{code}
  data Even : ℕ → Set where
    isEven0   : Even 0
    isEven+2  : ∀ {n} → Even n → Even (suc (suc n))
\end{code}
%
Next we may want to prove properties of this definition:
%
\begin{code}
  even+ : Even n → Even m → Even (n + m)
  even+    isEven0       e2  = e2
  even+ (  isEven+2 e1)  e2  = isEven+2 (even+ e1 e2)
\end{code}
%
Note that we omit universally quantified implicit arguments from the
typeset version of this paper, in accordance with convention used by
Haskell~\citep{haskell-report} and Idris~\citep{idris}.

As shown by Van der Walt and Swierstra~\citep{van-der-walt}, it is easy
to decide the |Even| property for closed terms using proof by
reflection. The interesting terms, however, are seldom closed.  For
instance, if we would like to use the |even+| lemma in the proof
below, we need to call it explicitly.

\begin{code}
  trivial : Even n → Even (n + 2)
  trivial e = even+ e (isEven+2 isEven0)
\end{code}
Manually constructing explicit proof objects
in this fashion is not easy. The proof is brittle. We cannot easily
reuse it to prove similar statements such as |Even (n + 4)|. If we
need to reformulate our statement slightly, proving |Even (2 + n)|
instead, we need to rewrite our proof. Proof automation can make
propositions more robust against such changes.

Coq's proof search tactics, such as |auto|, can be customized with a
\emph{hint database}, a collection of related lemmas. In our
example, |auto| would be able to prove the |trivial| lemma, provided
the hint database contains at least the constructors of the |Even|
data type and the |even+| lemma.
In
contrast to the construction of explicit proof terms, changes to the
theorem statement need not break the proof. This paper shows how to
implement a similar tactic as an ordinary function in Agda.

Before we can use our |auto| function, we need to construct a hint
database:
\review{I wondered whether the definition of even+ is expanded before added to the database. It only became clear later that only a name is added. It is better to clarify that here.}
\begin{code}
  hints : HintDB
  hints =
    [] << quote isEven0 << quote isEven+2 << quote even+
\end{code}
To construct such a database, we |quote| any terms that we wish to
include in it and pass them to the |_<<_| function, that constructs
a hint database from an appropriate sequence of names.  We will
describe the implementation of the |hintdb| function further in
Section~\ref{sec:hintdbs}. Note, however, that unlike Coq, the hint
data base is a \emph{first-class} value that can be manipulated,
inspected, or passed as an argument to a function.

We now give an alternative proof of the |trivial| lemma using the
|auto| tactic and the hint database defined above:
\begin{code}
  trivial : Even n → Even (n + 2)
  trivial = quoteGoal g in unquote (auto 5 hints g)
\end{code}
Or, using the newly added Agda tactic syntax\footnote{
  Syntax for Agda tactics was added in Agda 2.4.2.
}:
\begin{code}
  trivial : Even n → Even (n + 2)
  trivial = tactic (auto 5 hints)
\end{code}
The notation |tactic f| is simply syntactic sugar for |quoteGoal g in
unquote (f g)|, for some function |f|.

The central ingredient is a \emph{function} |auto| with the following
type:
\begin{code}
  auto : (depth : ℕ) → HintDB → Term → Term
\end{code}
Given a maximum depth, hint database, and goal, it searches for a
proof |Term| that witnesses our goal. If this term can be found, it is
spliced back into our program using the |unquote| statement.

Of course, such invocations of the |auto| function may fail. What
happens if no proof exists? For example, trying to prove |Even n →
Even (n + 3)| in this style gives the following error:
\begin{verbatim}
  Exception searchSpaceExhausted !=<
    Even .n -> Even (.n + 3) of type Set
\end{verbatim}
When no proof can be found, the |auto| function generates a dummy
term with a type that explains the reason the search has failed. In
this example, the search space has been exhausted. Unquoting this
term, then gives the type error message above. It is up to the
programmer to fix this, either by providing a manual proof or
diagnosing why no proof could be found.

\todo{Summarize working of auto:

* Quote goal to Agda Term;
* Convert Agda Term to PSTerm
* Proof search with hint database
* Convert proof to Agda Term
* Unquote agda term

Proof search uses unification, must be first order

Bounded depth, proof must be constructed from hints in db (and context?)
no recursive function calls created automatically



But the biggest problem is that the paper doesn't clearly separate
what in the code is a good idea, what is an engineering trick, and
what is wart required to satisfy Agda. A discussion at that level
would be very informative and useful.

Tricks + Warts
* Finite types, shifting indices, Generation of fresh variables
* 'Plumbing' reflection-conversion
* Proof obligations? regarding syntax
* constructing incomplete proofs

}

The remainder of this paper will explain how this |auto| function is
implemented.



%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
