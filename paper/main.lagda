\documentclass[preprint,draft]{sigplanconf}

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
  Proof automation is important. Custom tactic languages are hacky. We
  show how proof automation can be programmed in a general purpose
  dependently typed programming language using reflection. This makes
  it easier to automate, debug, and test proof automation.\todo{Write
    good abstract}
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
Agda's reflection mechanism~\cite{van-der-walt}, developers can write
powerful automatic decision procedures~\cite{allais}. Unfortunately,
not all proofs are easily automated in this fashion. When this is the
case, the user is forced to interact with the integrated development
environment and manually construct a proof term step by step.

This paper tries to combine the best of both worlds by implementing
a library for proof search \emph{within} Agda itself. More specifically,
this paper makes the following novel contributions:

\begin{itemize}
\item %
  After illustrating the usage of our library with several motivating
  examples (Section~\ref{sec:motivation}), we show how to implement a
  Prolog interpreter in the style of \citet{stutterheim} in Agda
  (Section~\ref{sec:prolog}). Note that, in contrast to Agda,
  resolving a Prolog query need not terminate. Using coinduction,
  however, we can write an interpreter for Prolog that is \emph{total}.
\item %
  Resolving a Prolog query results in a substitution that, when applied
  to the goal, produces a term that can be derived from the given
  rules. We extend our interpreter to produce a proof term that
  witnesses the validity of the resulting substitution
  (Section~\ref{sec:proofs}).
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
  lightweight type classes in Agda
  (Section~\ref{sec:type-classes}). This resolves one of the major
  restrictions of instance arguments: the lack of recursively search
  procedure for their construction.
\end{itemize}

All the code described in this paper is freely available from
GitHub\footnote{
  See \url{https://github.com/pepijnkokke/AutoInAgda}.
}. It is important to emphasize that all our code
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

The central type in the reflection mechanism is a type |Term : Set|
that defines an abstract syntax tree for Agda terms. There are several
language constructs for quoting and unquoting program fragments. The simplest
example of the reflection mechanism is the quotation of a single
term. In the definition of |idTerm| below, we quote the identity
function on Boolean values.
\begin{code}
  idTerm : Term
  idTerm = quoteTerm (\ (x : Bool) -> x)
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
  const : ∀ {a b} -> a  -> b -> a
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
|g|. When completing this definition by filling in the hole labelled
|0|, we may now refer to the variable |g|. This variable is bound to
to |def ℕ []|, the |Term| representing the type |ℕ|.

\subsection*{Using proof automation}

To illustrate the usage of our proof automation, we begin by defining a
predicate |Even| on natural numbers as follows:

\begin{code}
  data Even : ℕ → Set where
    Base : Even 0
    Step : ∀ {n} → Even n → Even (suc (suc n))
\end{code}
%
Next we may want to prove properties of this definition:
%
\begin{code}
  even+ : Even n → Even m → Even (n + m)
  even+ Base       e2  = e2
  even+ (Step e1)  e2  = Step (even+ e1 e2)
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
  simple e = even+ e (Step Base)
\end{code}
Manually constructing explicit proof objects
in this fashion is not easy. The proof is brittle. We cannot easily
reuse it to prove similar statements such as |Even (n + 4)|. If we
need to reformulate our statement slightly, proving |Even (2 + n)|
instead, we need to rewrite our proof. Proof automation can make
propositions more robust against such changes.

Coq's proof search tactics, such as |auto|, can be customized with a
\emph{hint database}, containing a collection of lemmas. In our
example, |auto| would be able to prove the |simple| lemma, provided it
the hint database contains at least the constructors of the |Even|
data type and the |even+| lemma.
The resulting proof is robust against reformulation and refactoring. In
contrast to the construction of explicit proof terms, changes to the
theorem statement need not break the proof. This paper shows how to
implement such a tactic similar to |auto| in Agda.

Before we can use our |auto| function, we need to construct a hint
database:
\begin{code}
  hints : HintDB
  hints = hintdb
    (quote Base :: quote Step :: quote even+ :: [])
\end{code}
To construct such a database, we |quote| any terms that we wish to
include in it and pass them to the |hintdb| function.  We
defer any discussion about the |hintdb| function for the moment. Note,
however, that unlike Coq, the hint data base is a \emph{first-class}
value that can be manipulated, inspected, or passed as an argument to
a function.

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
  Err searchSpaceExhausted !=<
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

\section{Prolog in Agda}
\label{sec:prolog}

Let us set aside Agda's reflection mechanism for the moment. In this
section, we will present a standalone Prolog
interpreter. Subsequently, we will show how this can be combined with
the reflection mechanism and suitably invoked in the definition of the
|auto| function. The code in this section is contained in its own Agda
module, parameterized by two sets:

> module Prolog 
>    (TermName : Set) (RuleName : Set) where

\subsection*{Terms and Rules}

The heart of our proof search implementation is the structurally
recursive unification algorithm described by~\citet{unification}. Here
the type of terms is indexed by the number of variables a given term
may contain. Doing so enables the unification algorithm to formulated
by structural induction on the number of free variables. This yields
the following definition of terms:
\begin{code}
data PrologTerm (n : ℕ) : Set where
  var  : Fin n → PrologTerm n
  con  : TermName → List (PrologTerm n) 
         → PrologTerm n
\end{code}
In addition to variables, we will encode first-order constants as a
|TermName| with a list of arguments.

For instance, if we choose to instantiate the |TermName| with the
following |Arith| data type, we can encode numbers and simple
arithmetic expressions:
\begin{code}
data Arith : Set where
  Suc   : Arith
  Zero  : Arith
  Add   : Arith
\end{code}
The closed term corresponding to the number one could be written as follows:
\begin{code}
One : PrologTerm 0
One = con Suc (con Zero ∷ [])
\end{code}
Similarly, we can use the |var| constructor to represent open terms,
such as |x + 1|. We use the prefix operator |#| to convert from
natural numbers to finite types:
\begin{code}
AddOne : PrologTerm 1
AddOne = con Add (var (# 0) ∷ con One ∷ [])
\end{code}
Note that this representation of terms is untyped. There is no check
that enforces addition is provided precisily two arguments. Although
we could add further type information to this effect, this introduces
additional overhead without adding safety to the proof automation
presented in this paper. For the sake of simplicity, we have therefore
chosen to work with this untyped definition.

We shall refrain from further discussion of the unification algorithm itself.
Instead, we restrict ourself to presenting the interface that we will use:
\begin{code}
  unify  : (t₁ t₂ : PrologTerm m) → Maybe (∃ (Subst m))
\end{code}
Substitutions are indexed by two natural numbers |n| and |m|. A
substitution of type |Subst m n| can be applied to a |PrologTerm m| to
produce a value of type |PrologTerm n|. The |unify| function takes two
terms |t₁| and |t₂| and tries to compute the most general unifier. As
unification may fail, the result is wrapped in the |Maybe| monad. The
number of variables in the terms resulting from the unifying
substition is not known \emph{a priori}, hence this number is
existentially quantified over.

This unification function is defined using an accumulating parameter,
representing an approximation of the final substitution. In what
follows, we will use the following, more general, function:
\begin{code}
  unifyAcc  : (t₁ t₂ : PrologTerm m) ->
            ∃ (Subst m) → Maybe (∃ (Subst m))
\end{code}

Next we define Prolog rules as records containing a name and terms for its
premises and conclusion:
\begin{code}
  record Rule (n : ℕ) : Set where
    field
      name        : RuleName
      conclusion  : PrologTerm n
      premises    : List (PrologTerm n)
\end{code}
Again the data type is quantified over
the number of variables used by its constituents. Note that variables
are shared between the premises and conclusion.

Using our newly defined |Rule| we can give a simple definition of
addition. In Prolog, this would be written as follows.
\begin{verbatim}
  add(0, x, x).
  add(x, y, z) :- add(suc(x), y, suc(z)).
\end{verbatim}
Unfortunately, the named equivalents in our Agda implementation are a
bit more verbose. Note that we have, for the sake of this example,
instantiated the |RuleName| and |TermName| to |String| and |Arith|
respectively.
\begin{code}
AddBase : Rule 1
AddBase = record {
  name        = "AddBase"
  conclusion  = con Add  (  Zero
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
  conclusion  =  con Add  (  var (# 0)
                          ∷  var (# 1)
                          ∷  var (# 2)
                          ∷ [])
  premises    =  con Add  (  con Suc (var (# 0) ∷ [])
                          ∷  var (# 1)
                          ∷  con Suc (var (# 2) ∷ [])
                          ∷ [])
                 ∷ []
  }
\end{code}

Lastly, before we can implement some form of proof search, we
define a pair of auxiliary functions. During proof
resolution, we will need to work with terms and rules containing a
different number of variables. We will use the following pair of
functions, |inject| and |raise|, to weaken bound variables, that is,
map values of type |Fin n| to some larger finite type.
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
that work on our |Rule| and |Term| data types, by mapping them over
all the variables that they contain.

\subsection{Proof search}

Our implementation of proof search is split into two steps.  In the
first step we set up an higher-order representation of the search
space, where we branch over some collection of undetermined rules at
every step. In the second step we flatten this abstract representation
to a concrete first-order search tree.

The distinction between these two phases keeps the nitty
gritty details involved with unification and weakening used in the
first phase separate from the actual proof search. By doing so, we can
implement various search strategies, such as breadth-first search,
depth-first search or an heuristic-driven algorithm, by simply
traversing the final search tree in a different order.

\subsubsection*{Setting up the search space}

We start by defining the following type synonym to distinguish goals
from regular Prolog terms:
\begin{code}
  Goal : ℕ → Set
  Goal n = Term n
\end{code}

Next we define the data type that we will use to model the
abstract search space.
\begin{code}
  data SearchSpace (m : ℕ) : Set where
    done  : Subst (m + δ) n → SearchSpace m
    step  : (∃ Rule → ∞ (SearchSpace m)) 
          → SearchSpace m
\end{code}
Ignoring the indices for the moment, the |SearchSpace| type has two
constructors: |done| and |step|. In the first case, we have found a
substitution that resolves the goal we are trying to prove. In the
|step| constructor, we have not yet resolved the goal, and instead
have a choice of which |Rule| to apply. Note that we do not specify
\emph{which} rules may be used; only how the choice of \emph{any} rule
determines the remainder of the search. As a search need not
terminate, the |SearchSpace| resulting from applying a rule are marked
as coinductive.

Now let us turn our attention to the indices. The variable |m| denotes
the number of variables in the goal; |δ| denotes the number of fresh
variables necessary to apply a rule; and |n| will denote the number of
variables remaining after we have resolved the goal. This naming will
be used consistently in subsequent definitions.

We can define a trivial |SearchSpace| that fails to return a
substitution:
\begin{code}
  fail : SearchSpace m
  fail = step (λ _ → ~ fail)
\end{code}
\wouter{Is dit niet een beetje lelijk? Kunnen we dan niet beter een
  Fail toevoegen aan de search space?}
Note that we rename Agda's notation for coinduction to more closely
resemble notation already familiar to Haskell programmers. Coinductive
suspensions are created with the prefix operator |~| rather than |♯|;
such suspensions can be forced using a bang, |!|, rather than the
usual |♭|.

We can now define a function |resolve| that will be in charge of building
up a value of type |SearchSpace| from an initial goal:
\begin{code}
  resolve : ∀ {m} -> Goal m → SearchSpace m
  resolve {m} g = resolveAcc (just (m , nil)) [ g ]
\end{code}
The |resolve| function is once again defined by calling an auxiliary
function defined using an accumulating parameter. It starts with an empty
substitution and a list of goals that only contains the initial goal
|g|. The |resolveAcc| function will attempt to resolve a list of
sub-goals, accumulating a substitution along the way:
\begin{code}
  resolveAcc  : ∀ {m δ : ℕ} 
    → Maybe (∃ (λ n → Subst (m + δ) n))
    → List (Goal (m + δ)) → SearchSpace m
  resolveAcc (just (n , subst))  []              = done subst
  resolveAcc nothing         _                   = fail
  resolveAcc (just (n , subst))  (goal ∷ goals)  = step next
\end{code}
If we have no remaining goals, we can use the |done| constructor to
return the substitution we have accumulated so far. If at any point,
however, the conclusion of the chosen rule was not unifiable with the
next open subgoal---and thus the accumulating parameter has become
|nothing|---the search will fail. The only interesting case is the
third one. If there are remaining goals to resolve, we recursively
construct a new |SearchSpace|. To do so, we use the |step| constructor
and branch over the choice of rule. The |next| function defined below
computes the remainder of the |SearchSpace| after trying to apply a
given rule:
\begin{code}
  next : ∃ Rule → ∞ (SearchSpace m)
  next (δ' , rule) = 
    ~ resolveAcc mgu (newGoals ++ oldGoals)
    where
      mgu   : Maybe (∃ (λ n → Subst (m + (δ + δ')) n))
      mgu   = unifyAcc goal' concl' subst'
        where
          goal'    : PrologTerm (m + (δ + δ'))
          goal'    = injectTerm δ' goal

          subst'    : ∃ (Subst (m + (δ + δ')))
          subst'    = n + δ' , injectSubst δ' subst

          concl'  : PrologTerm (m + (δ + δ'))
          concl'  = raiseTerm (m + δ) (conclusion rule)

      oldGoals   : List (PrologTerm (m + (δ + δ')))
      oldGoals   = injectTermList δ' goals

      newGoals  : List (PrologTerm (m + (δ + δ')))
      newGoals  = raiseTermList (m + δ) (premises rule)
\end{code}
For the moment, try to ignore the various calls to |raise| and
|inject|.  Given the |rule| that we must be applied, the |next|
function computes most general unifier of the conclusion of |rule| and
our current |goal|. The resulting substitution is passed to
|resolveAcc|, which continues the construction of the
|SearchSpace|. The premises of the |rule| are added to the list of
open goals that must be resolved. The apparent complexity of the
|next| function comes from the careful treatment of variables.

First of all, note that we pass the substitution accumulated so far to
|unifyAcc|. This ensures that this substitution is applied to the two
terms being unified.

\wouter{Tot hier ben ik zo'n beetje.}

Next, there is the problem of avoiding variable capture. We can only
unify two terms that are built up over the same set of
variables. Therefore we must ensure that the goal, the rule's
conclusion and its premises share a common set of variables.  However,
if we want the resulting substitution to have any meaning, we would
like the variables used in the initial goal term to remain the
same. This is where |inject| and |raise| come in.

Recall that injecting a variable into a larger set would keep its
value the same, whereas raising would raise the variable into the
portion of the set that was previously inaccessible. Therefore we will
always take care to |inject| our goal terms, and our accumulating
substitution, whereas we will |raise| the terms in the applied
rule.

Note that $\delta_2$ (the number of free variables in the chosen rule)
is added to $\delta_1$ (the amount of space that had to be made for
previous rule applications). This means that the amount of space to be
made will grow throughout the proof search.

\subsubsection*{Constructing search trees}

The second step in our proof search implementation is to transform the
|SearchSpace| we have just constructed into an N-ary tree. We do this
by branching once for every rule, at every |step| constructor.
The result of this transformation shall be expressed in terms of the
following data type.
\begin{code}
data SearchTree (A : Set) : Set where
  fail  : SearchTree A
  retn  : A → SearchTree A
  fork  : ∞ (List (SearchTree A)) → SearchTree A
\end{code}
In our case, the type |A| becomes a tuple containing the substitution
that was our previous result, together with a trace that keeps track
of all the applied tules. In order to keep the code readable, let us
introduce the following alias.\footnote{
  |Rules| is an alias for a list of existentially quantified rules
  |List (∃ Rule)|.
}
\begin{code}
  Result m  = ∃₂ (λ δ n → Subst (m + δ) n) × Rules
\end{code}

The function that takes care of the transformation is almost
trivial. For a given set of rules, we simply traverse the
|SearchSpace| structure, where at every |step| we apply the
continuation to every rule. However, since we also wish to maintain a
rule trace, we shall define this transformation using an
\pepijn{Did we mention that we'd use implicit universal quantification
  yet? Because I am slowly moving towards this notation.}\wouter{No, we should do so much earlier - beginning of section 3 or so. We should also adapt all code to follow the same convention.}
\begin{code}
mkTree : Rules → SearchSpace m → SearchTree (Result m)
mkTree rs₀ s = mkTreeAcc rs₀ s []
\end{code}
The |mkTree| function is defined using an helper with an accumulating
parameter, which keeps track of the applied rules.

\begin{code}
mkTreeAcc : Rules → SearchSpace m → Rules → SearchTree (Result m)
mkTreeAcc rs₀ (done s)  ap  = retn (s , ap)
mkTreeAcc rs₀ (step f)  ap  =
  fork (~ map (λ r → mkTreeAcc rs₀ (! f r) (ap ∷ʳ r)) rs₀)
\end{code}

\wouter{Hier een voorbeeld waar je speelt met het wel/niet mogen
  toepassen van bepaalde regels}

After the transformation, we are left with a simple tree structure,
for which we can define simple traversal strategies, such as
depth-first search (shown below) or breadth-first search (not shown,
but implemented).

\begin{code}
  dfs : (depth : ℕ) → SearchTree A → List A
  dfs  zero    _          = []
  dfs (suc k)  fail       = []
  dfs (suc k)  (retn x)   = return x
  dfs (suc k)  (fork xs)  = concatMap (dfs k) (! xs)
\end{code}

Putting it all together, we can define a function |searchToDepth|,
which implements proof search up to a given depth |d|, i.e.\ it
constructs the |SearchSpace|, converts it to a |SearchTree|, and
searches this tree (in this case using |dfs|) up to depth |d|.

\begin{code}
searchToDepth :
  ∀ {m} → ℕ → Rules → Goal m → List (Result m)
searchToDepth depth rules goal =
  dfs depth (mkTree rules (resolve goal))
\end{code}



\section{Constructing proof trees}
\label{sec:proofs}

In the previous section we have discussed the implementation of proof
search, returning a substitution which, when applied to the goal, will
provide the user with a variable-free term \pepijn{should probably
change or remove this bit}.

Another piece of information which was returned by the proof search
was a trace of the applied rules. In the following section we will
discuss using this information to reconstruct a proof term. That
is, we will construct terms of the following type, the type of closed
terms.
\begin{code}
data ProofTerm : Set where
  con : RuleName → List ProofTerm → ProofTerm
\end{code}
Since we know the arity of every rules (as we can simply count the
number of premises), the algorithm for reconstructing these terms is
simple.

We start from the back of the trace. Our invariant is that the trace
corresponds to a valid proof, and thus we know that the last rule
\emph{must} have an arity of zero. And thus we can safely turn it into
a proof term with an empty argument list.

We continue with the next-to-last argument, knowing that it may be a
rule with either an arity of zero (in which case we add it to the list
of proof terms) or an arity of one (in which case we give it the
proof term generated in the previous step as an argument).

The algorithm continues in this fashion until all we reach the first
rule in the trace, at which point our invariant states that our list
should contain exactly one element.

A downside of our current implementation is that we do not explicitly
encode this invariant, and thus we cannot define the proof term
construction as a total function. The case in the |toProofTerms|
function that cannot occur is marked with a comment, and our top-level
|toProofTerm| function is forced to return a |Maybe| value. This is
not a great downside as, due to the undecidability of first-order
proof search in general, we would have had to return a |Maybe| value
in any case \pepijn{should get rid of the term maybe-value; write an
incomplete/non-total function?}.

\begin{code}
toProofTerms : Rules → List ProofTerm
toProofTerms = foldr next []
  where
    next : ∃ Rule → List ProofTerm → List ProofTerm
    next (δ , r) pfs with arity r ≤? length pfs
    ... | no   r>p = [] -- should not occur
    ... | yes  r≤p =
      con (name r) (take (arity r) pfs) ∷ drop (arity r) pfs
\end{code}

\begin{code}
toProofTerm : Rules → Maybe ProofTerm
toProofTerm rs with toProofTerms rs
... | []     = nothing
... | p ∷ _  = just p
\end{code}



\section{Adding reflection}
\label{sec:reflection}

What remains is to give a pair of functions |to| and |from| which can
convert from |Reflection|'s |Term| data type to our first-order
|PrologTerm| data type and vice versa.

The first thing we will need if we are to provide such functions are
two concrete definitions for the |TermName| and |RuleName| data types.
It would be desirable to identify both types with Agda's |Name| type,
but unfortunately the Agda does not assign a name to the function
symbol $\_\!\!\to\!\!\_$, nor does it assign names to
variables. Therefore we will define two name data types, which handle
these cases.

Note that the |pvar| constructor has nothing to do with |PrologTerm|'s
|var| constructor; it is not used to construct a variable, but to use
an Agda variable as a Prolog constant. Its index $i$ is used in a
similar manner to Prolog variables, where two variables with the same
index are considered to have the same referent.
\begin{code}
data TermName : Set where
  pname  : (n : Name) → TermName
  pvar   : (i : ℕ) → TermName
  pimpl  : TermName
\end{code}
Conversely, the |rvar| constructor is used to be able to use Agda
variables as rules. Therefore, its index $i$ is used as a de Bruijn
index---its value can be used directly as an argument to |var| in
Agda's |Term| data type.
\begin{code}
data RuleName : Set where
  rname  : (n : Name) → RuleName
  rvar   : (i : ℕ) → RuleName
\end{code}
Last, we need one more auxiliary function, which we call |match|. This
function implements the intuition that if we have two data structures
limited to $m$ and $n$ variables, respectively, we should be able to
encode either with at most $m ⊔ n$ variables.

Below we present the reader with a sketch of the implementation of
|match| for finite sets.\todo{As to the |compare| function, the stdlib
mentions it is taken from "View from the left" by McBride \&
McKinna. Maybe we should turn this into an actual reference?}
\begin{code}
match : Fin m → Fin n → Fin (m ⊔ n) × Fin (m ⊔ n)
match i j with compare m n
match i j | less     .m k  = (inject (suc k) i , j)  -- n ≡ suc (m + k)
match i j | equal    .m    = (i , j)                 -- n ≡ m
match i j | greater  .n k  = (i , inject (suc k) j)  -- m ≡ suc (n + k)
\end{code}
Using this function we define the derived functions |matchTerms|,
which matches two terms, and |matchTermAndList|, which matches a term
to a list of terms.



\subsection*{Constructing terms}

An overview of the term conversion algorithm is as follows:
\begin{itemize}
\item %
  the algorithm traverses the abstract syntax tree, keeping track of
  how many function types have been passed, i.e.\ it keeps track of the
  current depth w.r.t.\ used de Bruijn indices;
\item %
  variables are converted using a customisable |fromVar| function,
  which is allowed to use the current depth;
\item %
  applications of definitions and constructors are converted using a
  customisable |fromDef| function;
\item %
  all function symbols $\_\!\!\to\!\!\_$ are converted to constant
  applications of the |pimpl| symbol, and for visible arguments the
  traversal of the right sub-tree continues with an increased depth;
\item %
  any other term (i.e.\ higher-order variables, lambda abstractions,
  instances of |unknown|) trigger an |unsupportedSyntax| error.
\end{itemize}
A sketch of the conversion function is presented below. Note that for
the combination of two sub-terms, we first ensure that their domains
match.
\begin{code}
fromTerm : ℕ → Term → Error (∃ PrologTerm)
fromTerm d (var i [])    = fromVar d i
fromTerm d (con c args)  = fromDef c ⟨$⟩ fromArgs d args
fromTerm d (def f args)  = fromDef f ⟨$⟩ fromArgs d args
fromTerm d (pi (arg visible _ (el _ t₁)) (el _ t₂))
  with fromTerm d t₁ | fromTerm (suc d) t₂
... | left msg         | _         = left msg
... | _                | left msg  = left msg
... | right (n₁ , p₁)  | right (n₂ , p₂)
  with matchTerms p₁ p₂
... | (p₁′ , p₂′) = right (n₁ ⊔ n₂ , con pimpl (p₁′ ∷ p₂′ ∷ []))
fromTerm d (pi (arg _ _ _) (el _ t₂)) = fromTerm (suc d) t₂
fromTerm _ _  = left unsupportedSyntax
\end{code}
The |fromArgs| function converts a list of |Term| arguments to a list
of Prolog terms, by stripping the |arg| constructor and recursively
applying the |fromTerm| function. Note that it filters non-visible
arguments.
\begin{code}
fromArgs : ℕ → List (Arg Term) → Error (∃ (List ∘ PrologTerm))
fromArgs d [] = right (0 , [])
fromArgs d (arg visible _ t ∷ ts) with fromTerm d t | fromArgs d ts
... | left msg       | _              = left msg
... | _              | left msg       = left msg
... | right (m , p)  | right (n , ps) with matchTermAndList p ps
... | (p′ , ps′)                      = right (m ⊔ n , p′ ∷ ps′)
fromArgs d (arg _ _ _ ∷ ts)           = fromArgs d ts
\end{code}
Next, the |fromDef| function simply constructs a first-order constant.
\begin{code}
fromDef : Name → ∃ (λ n → List (PrologTerm n)) → ∃ PrologTerm
fromDef f (n , ts) = n , con (pname f) ts
\end{code}
Last, the |fromVar| function converts de Bruijn variables from the
abstract syntax tree to Prolog style named variables. It does this by
taking the difference between the current depth and the index as the
variable name.
\begin{code}
fromVar : ℕ → ℕ → Error (∃ PrologTerm)
fromVar d i with compare d i
... | less     _ k  = left indexOutOfBounds
... | equal    _    = right (1     , var zero
... | greater  _ k  = right (suc k , var (fromℕ k))
\end{code}
Putting it all together, we are left with simple function that sends
Agda |Terms|s to |PrologTerm|s.
\begin{code}
toPrologTerm : Term → PrologTerm
toPrologTerm = fromTerm 0
\end{code}



\subsection*{Constructing rules}

Our next goal is to construct rules; or, more specifically, to convert
the quoted |Name|'s we would like to keep in our hint databases to
useful Prolog rules.
For this we will need to define two auxiliary functions. The first,
|fromName|, converts an Agda |Name| to a |PrologTerm|. It does this by
requesting the corresponding |Type|, stripping the outermost
constructor |el|, and converting the resutling Agda |Term|.
\begin{code}
fromName : Name → Error (∃ PrologTerm)
fromName = toPrologTerm ∘ unel ∘ type
\end{code}
The second takes a |PrologTerm| and splits it at every outermost
occurrence of the function symbol |pimpl|. Note that it would be
possible to define this function directly on Agda's |Term| data type,
but defining it on the |PrologTerm| data type gives a much cleaner
definition.
\begin{code}
splitTerm : PrologTerm n → List (PrologTerm n)
splitTerm (con pimpl (t₁ ∷ t₂ ∷ [])) = t₁ ∷ splitTerm t₂
splitTerm t = t ∷ []
\end{code}
Using these auxiliary functions, we can now trivially construct rules
from names. We convert the |Name| to a |PrologTerm|, split it, take
the last element as the rule's conclusion, and the initial list as its
premises.
\begin{code}
toRule : Name → Error (∃ Rule)
toRule name with fromName name
... | left msg       = left msg
... | right (n , t)  = toRule′ (n , splitTerm t)
  where
    toRule′ : ∃ (List ∘ PrologTerm) → Error (∃ Rule)
    toRule′ (n , xs) with initLast xs
    toRule′ (n , ._)  | []        = left panic!
    toRule′ (n , ._)  | xs ∷ʳ' x  = right (n , rule (rname name) x xs)
\end{code}

\todo{mention existence and usage of the |rule| constructor.}

\pepijn{Should we mention alternatives for rule construction?
  Generating all possible partial applications; generating the rules
  only as an atomic rule |(fromName n) :- .| and adding function application
  and composition?}

\subsection*{Constructing goals}

The construction of goal terms differs slightly from the construction
of Prolog terms. To see why, imagine we would use the above function
for converting goal types as well as hints.

\todo{add example where treatment of variables fucks things up}

Therefore, we will need a slightly different treatment of variables in
goal types. The conversion algorithm is similar to the implementation
of |fromTerm| above, but one mayor difference is in the |fromVar|
function.
\begin{code}
fromVar′ : ℕ → ℕ → Error (∃ PrologTerm)
fromVar′  d i with compare d i
... | less    _ k = left indexOutOfBounds
... | equal   _   = right (0 , con (pvar 0) [])
... | greater _ k = right (0 , con (pvar k) [])
\end{code}
Using a definition of |fromTerm| which uses the definition of
|fromVar′| as just given, we can define a conversion function which
constructs goal terms.
\begin{code}
toGoal : Term → Error (∃ PrologTerm × Rules)
toGoal with fromTerm′ 0
... | left msg = left msg
... | right (n , p) with reverse (splitTerm p)
... | []       = left panic!
... | (t ∷ ts) = right ((n , t) , toRules 0 ts)
  where
    toRules : ℕ → List (PrologTerm n) → Rules
    toRules d [] = []
    toRules d (t ∷ ts) = (n , rule (rvar d) t []) ∷ toRules (suc d) ts
\end{code}



\subsection*{Reification of proof terms}

\begin{code}
fromProofTerm : ProofTerm → Term
fromProofTerm (con (rvar i) ps) = var i []
fromProofTerm (con (rname n) ps) with definition n
... | function x    = def n ∘ toArg ∘ fromProofTerm ⟨$⟩ ps
... | constructor′  = con n ∘ toArg ∘ fromProofTerm ⟨$⟩ ps
... | _             = unknown
  where
   toArg = arg visible relevant
\end{code}



\subsection*{Putting it all together}

\begin{code}
intros : Term → Term
intros = introsAcc (length args)
  where
    introsAcc : ℕ → Term → Term
    introsAcc  zero   t = t
    introsAcc (suc k) t = lam visible (introsAcc k t)
\end{code}

\begin{code}
HintDB : Set
HintDB = List (∃ Rule)

hintdb : List Name → HintDB
hintdb = concatMap (fromError ∘ toRule)
  where
    fromError : Error A → List A
    fromError = fromEither (const []) [_]
\end{code}

\todo{mention utility function |quoteMsg| which returns the AST of a
  message}
\todo{mention that we \emph{could} theoretically return, for instance,
the specific bit of syntax that is unsupported, but that since we
cannot quote the |Term| type, we cannot just pass the terms around.}

\begin{code}
auto : ℕ → HintDB → Term → Term
auto depth rules goalType
  with toGoal goalType
... | left msg = quoteMsg msg
... | right ((n , g) , args)
  with searchToDepth depth (args ++ rules) g
... | [] = quoteMsg searchSpaceExhausted
... | (_ , trace) ∷ _
  with toProofTerm trace
... | nothing = quoteMsg panic!
... | just p  = intros (fromProofTerm p)
\end{code}

\section{Type classes}
\label{sec:type-classes}

\todo{Give a bigger example of debugging/automated proving}

\section{Discussion}
\label{sec:discussion}

\pepijn{One ``problem'' with our current implementation of proof
  search is that, while we encode the maximum number of variables used
  in a term, we do not enforce that all variables are used. As a
  consequence of this, we cannot guarantee that the substitution
  obtained from a successful proof search will substitute \emph{all}
  variables. Since we don't actually \emph{use} the substitution
  though, this does not really bother use in using our Prolog library
  to define an |auto| tactic.}

\todo{Mention Idris}

Future work: auto rewrite; setoid rewrite; proof combinators.

limitations of using recursion in hint data base

Cf Agsy
Combining hint data bases (use $\_\plus\_$ :)
Debugging failed auto attempts, or other examples from
\url{http://adam.chlipala.net/cpdt/html/LogicProg.html}

We cannot `insert goals' in the term produced by a call to auto. This
could be useful if you want to allow a tactic to return an unfinished
proof. Or can we? \pepijn{Nope? I'm afraid I still don't understand
the concept of |auto| generating existentials (or |iauto|).}

Work with \emph{typed} term language. This is a hard problem.

Compare with Mtac.

Cite Devriese paper.

\bibliographystyle{plainnat}
\bibliography{main}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
