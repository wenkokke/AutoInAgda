\documentclass[preprint]{sigplanconf}

%include agda.fmt
%include main.fmt
\include{preamble}

\begin{document}

\conferenceinfo{ICFP'14} {September 1--3, 2014, G\"oteborg, Sweden}
\titlebanner{Under preparation for ICFP 2014}

\title{Auto in Agda}
\subtitle{Programming proof search}

\authorinfo{Pepijn Kokke \and Wouter Swierstra}
           {Universiteit Utrecht}
           {pepijn.kokke@@gmail.com \quad w.s.swierstra@@uu.nl}

\maketitle

\begin{abstract}

  As proofs in type theory become increasingly complex, there is a
  growing need to provide better proof automation. This paper shows
  how to implement a Prolog-style resolution procedure in the
  dependently typed programming language Agda. Connecting this
  resolution procedure to Agda's reflection mechanism provides a
  first-class proof search tactic for first-order Agda
  terms. Furthermore, the same mechanism may be used in tandem with
  Agda's instance arguments to implement type classes in the style of
  Haskell. As a result, writing proof automation tactics need not be
  different from writing any other program.
\end{abstract}

\section{Introduction}
\label{sec:intro}

Writing proof terms in type theory is hard and often tedious.
Interactive proof assistants based on type theory, such as
Agda~\cite{agda} or Coq~\cite{coq}, take very different approaches to
facilitating this process.

The Coq proof assistant has two distinct language fragments. Besides
the programming language Gallina, there is a separate tactic language
for writing and programming proof scripts. Together with several
highly customizable tactics, the tactic language Ltac can provide
powerful proof automation~\cite{chlipala}. Having to introduce a
separate tactic language, however, seems at odds with the spirit of
type theory, where a single language is used for both proof and
computation.  Having a separate language for programming proofs has
its drawbacks. Programmers need to learn another language to automate
proofs. Debugging Ltac programs can be difficult and the resulting
proof automation may be inefficient~\cite{brabaint}.

Agda does not have Coq's segregation of proof and programming
language.  Instead, programmers are encouraged to automate proofs by
writing their own solvers~\cite{ulf-tphols}. In combination with
Agda's reflection mechanism~\cite{agda-relnotes-228,van-der-walt}, developers can write
powerful automatic decision procedures~\cite{allais}. Unfortunately,
not all proofs are easily automated in this fashion. In that case,
the user is forced to interact with the integrated development
environment and manually construct a proof term step by step.

This paper tries to combine the best of both worlds by implementing a
library for proof search \emph{within} Agda itself. More specifically,
this paper makes the several novel contributions.

\begin{itemize}
\item %
  We show how to implement a Prolog interpreter in the style of
  \citet{stutterheim} in Agda (Section~\ref{sec:prolog}). Note that,
  in contrast to Agda, resolving a Prolog query need not terminate.
  Using coinduction, however, we can write an interpreter for Prolog
  that is \emph{total}.
\item %
  Resolving a Prolog query results in a substitution that, when applied
  to the goal, produces a solution in the form of a term that can be
  derived from the given rules.
  We extend our interpreter to also produce a trace of the applied
  rules, which allow us to produce a proof term that is a witness to
  the validity of the resulting substitution (Section~\ref{sec:proofs}).
\item %
  We integrate this proof search algorithm with Agda's
  \emph{reflection} mechanism (Section~\ref{sec:reflection}). This
  enables us to \emph{quote} the type of a lemma we would like to
  prove, pass this term as the goal of our proof search algorithm, and
  finally, \emph{unquote} the resulting proof term, thereby proving
  the desired lemma.
\item %
  Finally, we show how we can use our proof search together with
  Agda's \emph{instance arguments}~\cite{instance-args} to implement
  lightweight type classes in Agda (Section~\ref{sec:type-classes}).
  This resolves one of the major restrictions of instance arguments:
  the lack of a recursive search procedure for their construction.
\end{itemize}

Although Agda already has built-in proof search
functionality~\cite{lindblad}, we believe that exploring the
first-class proof automation defined in this paper is still
worthwhile. For the moment, however, we would like to defer discussing
the various forms of proof automation until after we have
presented our work (Section~\ref{sec:discussion}).

All the code described in this paper is freely available from
GitHub.\footnote{
  See \url{https://github.com/pepijnkokke/AutoInAgda}.
} It is important to emphasize that all our code
is written in the safe fragment of Agda: it does not depend on any
postulates or foreign functions; all definitions pass Agda's
termination checker; and all metavariables are resolved.


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
metaprogramming in the style of Lisp~\cite{lisp-macros},
MetaML~\cite{metaml}, and Template
Haskell~\cite{template-haskell}. This reflection mechanisms make it
possible to convert a program fragment into its corresponding abstract
syntax tree and vice versa. We will introduce Agda's reflection
mechanism here with several short examples, based on the explanation
in previous work~\cite{van-der-walt}. A more complete overview can be
found in the Agda release notes~\cite{agda-relnotes-228} and Van der
Walt's thesis~\cite{vdWalt:Thesis:2012}.

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

More generally, the |quote| language construct allows users to access
the internal representation of an identifier, a value of a built-in
type |Name|. Users can subsequently request the type or definition of
such names.

Dual to quotation, the |unquote| mechanism allows users to splice in a
|Term|, replacing it with a its concrete syntax. For example, we could
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
to |def ℕ []|, the |Term| representing the type |ℕ|.

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
Haskell~\cite{haskell-report} and Idris~\cite{idris}.

As shown by Van der Walt and Swierstra~\cite{van-der-walt}, it is easy
to decide the |Even| property for closed terms using proof by
reflection. The interesting terms, however, are seldom closed.  For
instance, if we would like to use the |even+| lemma in the proof
below, we need to call it explicitly.

\begin{code}
  simple : Even n → Even (n + 2)
  simple e = even+ e (isEven+2 isEven0)
\end{code}
Manually constructing explicit proof objects
in this fashion is not easy. The proof is brittle. We cannot easily
reuse it to prove similar statements such as |Even (n + 4)|. If we
need to reformulate our statement slightly, proving |Even (2 + n)|
instead, we need to rewrite our proof. Proof automation can make
propositions more robust against such changes.

Coq's proof search tactics, such as |auto|, can be customized with a
\emph{hint database}, a collection of related lemmas. In our
example, |auto| would be able to prove the |simple| lemma, provided it
the hint database contains at least the constructors of the |Even|
data type and the |even+| lemma.
In
contrast to the construction of explicit proof terms, changes to the
theorem statement need not break the proof. This paper shows how to
implement a similar tactic as an ordinary function in Agda.

Before we can use our |auto| function, we need to construct a hint
database:
\begin{code}
  hints : HintDB
  hints =
    [] << quote isEven0 << quote isEven+2 << quote even+
\end{code}
To construct such a database, we |quote| any terms that we wish to
include in it and pass them to the |hintdb| function.  We
defer any discussion about the |hintdb| function
to Section~\ref{sec:hintdbs}. Note, however, that unlike Coq, the hint
data base is a \emph{first-class} value that can be manipulated,
inspected, or passed as an argument to a function.

We now give an alternative proof of the |simple| lemma, using this
hint database:
\begin{code}
  simple : Even n → Even (n + 2)
  simple = quoteGoal g in unquote (auto 5 hints g)
\end{code}
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
term whose type explains the reason why the search has failed. In
this example, the search space has been exhausted. Unquoting this
term, then gives the type error message above. It is up to the
programmer to fix this, either by providing a manual proof or
diagnosing why no proof could be found.

The remainder of this paper will explain how this |auto| function is
implemented.



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


\section{Adding reflection}
\label{sec:reflection}



\section{Type classes}
\label{sec:type-classes}

As a final application of our proof search algorithm, we show how it
can be used to implement a \emph{type classes} in the style of
Haskell. Souzeau and Oury~\cite{coq-type-classes} have already shown
how to use Coq's proof search mechanism to construct
dictionaries. Using Agda's \emph{instance
  arguments}~\cite{instance-args} and the proof search presented in
this paper, we mimic their results.

We begin by declaring our `type class' as a record containing the
desired function:
\begin{code}
record Show (A : Set) : Set where
  field
    show : A → String
\end{code}

We can write instances for the |Show| `class' by constructing explicit
dictionary objects:
\begin{code}
ShowBool  : Show Bool
ShowBool = record { show = ... }

Showℕ : Show ℕ
Showℕ = record { show = ... }
\end{code}
Using instance arguments, we can now call our |show| function without
having to pass the required dictionary explicitly:
\begin{code}
open Show {{...}}

example : String
example = show 3
\end{code}
The instance argument mechanism infers that the |show| function is
being called on a natural number, hence a dictionary of type |Show ℕ|
is required. As there is only a single value of type |Show ℕ|, the
required dictionary is inserted automatically. If we have multiple
instance definitions for the same type or omit the required instance
altogether, the Agda type checker would have given an error.

It is more interesting to consider parametrized instances, such as
the |Either| instance given below.
\begin{code}
ShowEither : Show A → Show B → Show (Either A B)
ShowEither ShowA ShowB = record { show = showE }
  where
    showE : Either A B -> String
    showE (left x)   = "left " ++ show x
    showE (right y)  = "right " ++ show y
\end{code}
Unfortunately, instance arguments do not do any recursive search for
suitable instances. Trying to call |show| on a value of type |Either ℕ
Bool|, for example, will not succeed: the Agda type checker will
complain that it cannot find a suitable instance argument. At the
moment, the only way to resolve this is to construct the required
instances manually:
\begin{code}
  ShowEitherBoolℕ : Show (Either Bool ℕ)
  ShowEitherBoolℕ = ShowEither ShowBool Showℕ
\end{code}
Writing out such dictionaries is rather tedious.

We can, however, use the |auto| function to construct the desired
instance argument automatically. We start by putting the desired
instances in a hint database:
\begin{code}
ShowHints : HintDB
ShowHints = hintdb  (quote ShowEither
                    ∷ quote ShowBool
                    ∷ quote Showℕ ∷ [])
\end{code}

The desired dictionary can now be assembled for us by calling the
|auto| function:
\begin{code}
example : String
example = show (left 4) ++ show (right true)
  where
    instance =  quoteGoal g
                in unquote (auto 5 ShowHints g)
\end{code}
Note that the type of the locally bound |instance| record is inferred
in this example. Using this type, the |auto| function assembles the
desired dictionary. When |show| is called on different types, however,
we may still need to provide the type signatures of the instances we
desire.
While deceptively simple, this example illustrates how \emph{useful}
it can be to have even a little automation.

\section{Discussion}
\label{sec:discussion}

The |auto| function presented here is far from perfect. This section
not only discusses its limitations, but compares it to existing proof
automation techniques in interactive proof assistants.

\paragraph{Performance}
First of all, the performance of the |auto| function is terrible. Any
proofs that require a depth greater than ten are intractable in
practice. This is an immediate consequence of Agda's poor compile-time
evaluation. The current implementation is call-by-name and does no
optimization whatsoever. While a mature evaluator is beyond the scope
of this project, we believe that it is essential for Agda proofs to
scale beyond toy examples. Simple optimizations, such as the erasure
of the natural number indexes used in unification~\cite{brady-opt},
would certainly help speed up the proof search.

\paragraph{Restrictions}
The |auto| function can only handle first-order terms. Even though
higher-order unification is not decidable in general, we believe that it
should be possible to adapt our algorithm to work on second-order
goals.
Furthermore, there are plenty of Agda features that are not
supported or ignored by our quotation functions, such as universe
polymorphism, instance arguments, and primitive functions.

Even for definitions that seem completely first-order, our |auto|
function can fail unexpectedly. Consider the following definition of
the product type, taken from Agda's standard library:
\begin{code}
_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)
\end{code}
Here a (non-dependent) pair is defined as a special case of the
type |Σ|, representing dependent pairs. We can define the obvious |Show|
instance for such pairs:
\begin{code}
Show× : Show A -> Show B -> Show (A × B)
\end{code}
Somewhat surprisingly, trying to use this rule to create an instance
of the |Show| `class' fails. The |quoteGoal| construct always returns
the goal in normal form, which exposes the higher-order nature of
|A × B|.  Converting the goal |Show (A × (λ _ → B))| to a |PrologTerm|
will raises the `exception' |unsupportedSyntax|; the goal type
contains a lambda which we cannot handle.

Furthermore, there are some limitations on the hints that may be
stored in the hint database. At the moment, we construct every hint by
quoting an Agda |Name|. Not all useful hints, however, have a such a
|Name|, such as any variables locally bound in the context by pattern
matching or function arguments. For example, the following call to the
|auto| function fails to produce the desired proof:
\begin{code}
  simple : Even n → Even (n + 2)
  simple e = quoteGoal g in unquote (auto 5 hints g)
\end{code}
The variable |e|, necessary to complete the proof is not part of the
hint database. We hope that this could be easily fixed by providing a
variation of the |quoteGoal| construct that returns both the term
representing to the current goal and a list of the terms bound in the
local context.

% Another restriction is that it is not currently possible to pass
% arguments to a hint database manually. For instance, see the following
% definition of |even+|:
% \begin{code}
% even+ : Even n → Even m → Even (n + m)
% even+ (isEven0) = quoteGoal g in unquote (auto 5 [] g)
% even+ (isEven+2 e) = quoteGoal g in unquote hole
% \end{code}
% Directly trying to add |e| to a hint database results in the error
% message ``\textbf{quote}: not a defined name''.
% Using |quoteTerm| on |e| returns |var 0 []|, which we could
% potentially use to construct a rule for the usage of |e|. However,
% there is currently no function in the Reflection API that enables us
% to obtain the type corresponding to a |Term|, and thus no way of
% constructing a rule based on |e|.
% A last resort, binding the variable |e| to a name in a where-clause,
% gives quite unexpected results: the invocation of |auto| is accepted
% through Agda's interactive interface, and can be shown to reduce to
% the correct definition:
% \begin{code}
%   λ z → isEven+2 (even+ind e z)
% \end{code}
% However, when recompiling the code using Agda's batch type-checker, it
% is rejected. \pepijn{Batch type-checker?}

\paragraph{Refinement}
The |auto| function returns a complete proof term or fails
entirely. This is not always desirable. We may want to return an
incomplete proof, that still has open holes that the user must
complete. This difficult with the current implementation of Agda's
reflection mechanism: it cannot generate an incomplete |Term|.

In the future, it may be interesting to explore how to integrate proof
automation, as described in this paper, better with Agda's IDE. If the
call to |auto| were to generate the concrete syntax for a (possibly
incomplete) proof term, this could be replaced with the current goal
quite easily. An additional advantage of this approach would be that
reloading the file does no longer needs to recompute the proof terms.

\paragraph{Metatheory}
The |auto| function is necessarily untyped because the interface of
Agda's reflection mechanism is untyped. Defining a well-typed
representation of dependent types in a dependently typed language
remains an open problem, despite various efforts in this
direction~\cite{james-phd,nisse,devriese,kipling}. If we had such a
representation, however, we might be able to use the type information
to prove that when the |auto| function succeeds, the resulting term
has the correct type. As it stands, proving soundness of the
|auto| function is non-trivial: we would need to define the typing
rules of Agda's |Term| data type and prove that the |Term| we produce
witnesses the validity of our goal |Term|.
It may be slightly easier
to ignore Agda's reflection mechanism and instead verify the
metatheory of the Prolog interpreter: if a proof exists at some given
depth, |searchToDepth| should find it; any |Result| returned by
|searchToDepth| should correspond to a valid derivation.

\subsection*{Related work}

There are several other interactive proof assistants, dependently
typed programming languages, and alternative forms of proof
automation in Agda. In the remainder of this section, we will briefly compare
the approach taken in this paper to these existing systems.

\paragraph{Coq}
Coq has rich support for proof automation. The Ltac language
and the many primitive, customizable tactics are extremely
powerful~\cite{chlipala}. Despite Coq's success, it is still
worthwhile to explore better methods for proof automation. Recent work
on Mtac~\cite{mtac} shows how to add a typed language for proof
automation on top of Ltac. Furthermore, Ltac itself is not designed to
be a general purpose programming language. It can be difficult to
abstract over certain patterns and debugging
proof automation is not easy. The programmable proof automation,
written using reflection, presented here may not be as mature as Coq's
Ltac language, but addresses  these issues.

\paragraph{Idris}
The dependently typed programming language Idris also has a collection
of tactics, inspired by some of the more simple Coq tactics, such as
|rewrite|, |intros|, or |exact|. Each of these tactics is built-in and
implemented as part of the Idris system. There is a small Haskell
library for tactic writers to use that exposes common commands, such
as unification, evaluation, or type checking. Furthermore, there are
library functions to help handle the construction of proof terms,
generation of fresh names, and splitting sub-goals. This approach is
reminiscent of the HOL family of theorem provers~\cite{hol} or Coq's
plug-in mechanism. An important drawback is that tactic writers need
to write their tactics in a different language to the rest of their
Idris code; furthermore, any changes to tactics requires a
recompilation of the entire Idris system.

\paragraph{Agsy}

Agda already has a built-in `auto' tactic that outperforms the |auto|
function we have defined here~\cite{lindblad}. It is nicely integrated
with the IDE and does not require the users to provide an explicit
hint database. It is, however, implemented in Haskell and shipped as
part of the Agda system. As a result, users have very few
opportunities for customization: there is limited control over which
hints may (or may not) be used; there is no way to assign priorities
to certain hints; and there is a single fixed search strategy. In
contrast to the proof search presented here, where we have much more
fine grained control over all these issues.

\subsection*{Closure}

The proof automation presented in this paper is not as mature as some
of these alternative systems. Yet we strongly believe that this style
of proof automation is worth pursuing further.

The advantages of using reflection to program proof tactics should be
clear: we do not need to learn a new programming language to write new
tactics; we can use existing language technology to debug and test our
tactics; and we can use all of Agda's expressive power in the design
and implementation of our tactics. If a particular problem domain
requires a different search strategy, this can be implemented by
writing a new traversal over a |SearchTree|. Hint databases are
first-class values. There is never any built-in magic; there are no
compiler primitives beyond Agda's reflection mechanism.

The central philosophy of Martin-L\"of type theory is that the
construction of programs and proofs is the same activity. Any
external language for proof automation renounces this philosophy. This
paper demonstrates that proof automation is not inherently at odds
with the philosophy of type theory. Paraphrasing
Martin-L\"of~\cite{martin-lof}, it no longer seems possible to
distinguish the discipline of \emph{programming} from the
\emph{construction} of mathematics.

% This is super useful: consider the problem of having |trans| in a hint
% database.


% Using the techniques described in this paper, it is possible to write
% many other pieces of proof automation. Automated rewriting, for
% example. Or a high-level, first-class tactic language: try this piece
% of automation, and if that fails try something else.

% This is the way forward for proof automation.

\paragraph{Acknowledgements}
We would like to thank the Software Technology Reading Club at the
Universiteit Utrecht for their helpful feedback.


\bibliographystyle{plainnat}
\bibliography{main}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
