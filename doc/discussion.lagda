\section{Discussion}
\label{sec:discussion}

The |auto| function presented here is far from perfect. This section
not only discusses its limitations, but compares it to existing proof
automation techniques in interactive proof assistants.

%% REASON:
%%  I removed the section on performance here, since we can and
%%  should tone it down a whole bunch. My rewrites and possibly Agda's
%%  new treatment of natural numbers as Haskell integers (if addition is
%%  treated as a Haskell operation) sped our tactic up a WHOLE bunch.
%%
%%\paragraph{Performance}
%%First of all, the performance of the |auto| function is terrible. Any
%%proofs that require a depth greater than ten are intractable in
%%practice. This is an immediate consequence of Agda's poor compile-time
%%evaluation. The current implementation is call-by-name and does no
%%optimisation whatsoever. While a mature evaluator is beyond the scope
%%of this project, we believe that it is essential for Agda proofs to
%%scale beyond toy examples. Simple optimizations, such as the erasure
%%of the natural number indexes used in unification~\cite{brady-opt},
%%would certainly help speed up the proof search.

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
type |Σ|, representing dependent pairs. Now consider 
the following trivial lemma:
\begin{code}
  andIntro : (A : Set) -> (B : Set) -> A × B
\end{code}
Somewhat surprisingly, trying to prove this lemma using our |auto|
function, providing the constructor of |Σ| types as a hint, fails. The
|quoteGoal| construct always returns the goal in normal form, which
exposes the higher-order nature of |A × B|.  Converting the goal |(A ×
(λ _ → B))| to a |PrologTerm| will raises the `exception'
|unsupportedSyntax|; the goal type contains a lambda which we cannot
handle.

Furthermore, there are some limitations on the hints that may be
stored in the hint database. At the moment, we construct every hint by
quoting an Agda |Name|. Not all useful hints, however, have a such a
|Name|, such as any variables locally bound in the context by pattern
matching or function arguments. For example, the following call to the
|auto| function fails to produce the desired proof:
\begin{code}
  trivial : Even n → Even (n + 2)
  trivial e = tactic (auto 5 hints)
\end{code}
The variable |e|, necessary to complete the proof is not part of the

hint database. The |tactic| keyword in the upcoming Agda release
addresses this, by providing both the current goal and a list of the
terms bound in the local context as arguments to the tactic functions.

%% REASON:
%%  This section was removed because it is no longer a restriction,
%%  since quoteContext was implemented.
%%
%%Another restriction is that it is not currently possible to pass
%%arguments to a hint database manually. For instance, see the following
%%definition of |even+|:
%%\begin{code}
%%even+ : Even n → Even m → Even (n + m)
%%even+ (isEven0) = quoteGoal g in unquote (auto 5 [] g)
%%even+ (isEven+2 e) = quoteGoal g in unquote hole
%%\end{code}
%%Directly trying to add |e| to a hint database results in the error
%%message ``\textbf{quote}: not a defined name''.
%%Using |quoteTerm| on |e| returns |var 0 []|, which we could
%%potentially use to construct a rule for the usage of |e|. However,
%%there is currently no function in the Reflection API that enables us
%%to obtain the type corresponding to a |Term|, and thus no way of
%%constructing a rule based on |e|.
%%A last resort, binding the variable |e| to a name in a where-clause,
%%gives quite unexpected results: the invocation of |auto| is accepted
%%through Agda's interactive interface, and can be shown to reduce to
%%the correct definition:
%%\begin{code}
%%  λ z → isEven+2 (even+ind e z)
%%\end{code}
%%However, when recompiling the code using Agda's batch type-checker, it
%%is rejected. \pepijn{Batch type-checker?}

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
direction~\citep{james-phd,nisse,devriese,kipling}. If we had such a
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
powerful~\citep{chlipala}. Despite Coq's success, it is still
worthwhile to explore better methods for proof automation. Recent work
on Mtac~\citep{mtac} shows how to add a typed language for proof
automation on top of Ltac. Furthermore, Ltac itself is not designed to
be a general purpose programming language. It can be difficult to
abstract over certain patterns and debugging
proof automation is not easy. The programmable proof automation,
written using reflection, presented here may not be as mature as Coq's
Ltac language, but addresses  these issues.

More recently, \cite{malecha} have designed a higher-order reflective
programming language (MirrorCore) and an associated tactic language
(Rtac). MirrorCore defines a unification algorithm -- similar to the
one we have (re)implemented in this paper. Alternative implementations
of several familiar Coq tactics, such as |eauto| and |setoid_rewrite|,
have been developed using Rtac. The authors have identified several
similar advantages of `programming' tactics, rather than using
built-in primitives that we mention in this paper, such as
manipulating and assembling first-class hint databases.

\paragraph{Idris}
The dependently typed programming language Idris also has a collection
of tactics, inspired by some of the more simple Coq tactics, such as
|rewrite|, |intros|, or |exact|. Each of these tactics is built-in and
implemented as part of the Idris system. There is a small Haskell
library for tactic writers to use that exposes common commands, such
as unification, evaluation, or type checking. Furthermore, there are
library functions to help handle the construction of proof terms,
generation of fresh names, and splitting sub-goals. This approach is
reminiscent of the HOL family of theorem provers~\citep{hol} or Coq's
plug-in mechanism. An important drawback is that tactic writers need
to write their tactics in a different language to the rest of their
Idris code; furthermore, any changes to tactics requires a
recompilation of the entire Idris system.

\paragraph{Agsy}

Agda already has a built-in `auto' tactic that outperforms the |auto|
function we have defined here~\citep{lindblad}. It is nicely integrated
with the IDE and does not require the users to provide an explicit
hint database. It is, however, implemented in Haskell and shipped as
part of the Agda system. As a result, users have very few
opportunities for customization: there is limited control over which
hints may (or may not) be used; there is no way to assign priorities
to certain hints; and there is a single fixed search strategy. In
contrast to the proof search presented here, where we have much more
fine grained control over all these issues.

\subsection*{Conclusion}

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
Martin-L\"of~\citep{martin-lof}, it no longer seems possible to
distinguish the discipline of \emph{programming} from the
\emph{construction} of mathematics.

% This is super useful: consider the problem of having |trans| in a hint
% database.


% Using the techniques described in this paper, it is possible to write
% many other pieces of proof automation. Automated rewriting, for
% example. Or a high-level, first-class tactic language: try this piece
% of automation, and if that fails try something else.

% This is the way forward for proof automation.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
