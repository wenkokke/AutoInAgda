\section{Introduction}
\label{sec:intro}

Writing proof terms in type theory is hard and often tedious.
Interactive proof assistants based on type theory, such as
Agda~\citep{agda} or Coq~\citeyearpar{coq}, take very different approaches to
facilitating this process.

The Coq proof assistant has two distinct language fragments. Besides
the programming language Gallina, there is a separate tactic language
for writing and programming proof scripts. Together with several
highly customizable tactics, the tactic language Ltac can provide
powerful proof automation~\citep{chlipala}. Having to introduce a
separate tactic language, however, seems at odds with the spirit of
type theory, where a single language is used for both proof and
computation.  Having a separate language for programming proofs has
its drawbacks. Programmers need to learn another language to automate
proofs. Debugging Ltac programs can be difficult and the resulting
proof automation may be inefficient~\citep{brabaint}.

Agda does not have Coq's segregation of proof and programming
language.  Instead, programmers are encouraged to automate proofs by
writing their own solvers~\citep{ulf-tphols}. In combination with
Agda's reflection mechanism~\citep{agda-relnotes-228,van-der-walt}, developers can write
powerful automatic decision procedures~\citep{allais}. Unfortunately,
not all proofs are easily automated in this fashion. In that case,
the user is forced to interact with the integrated development
environment and manually construct a proof term step by step.

This paper tries to combine the best of both worlds by implementing a
library for proof search \emph{within} Agda itself. In other words, we
have defined a \emph{program} for the automatic \emph{construction} of
\emph{mathematical} proofs. More specifically, this paper makes
several novel contributions.

\begin{itemize}
\item %
  We show how to implement a Prolog interpreter in the style of
  \citet{stutterheim} in Agda (Section~\ref{sec:prolog}). Note that,
  in contrast to Agda, resolving a Prolog query need not terminate.
  Using coinduction, however, we can write an interpreter for Prolog
  that is \emph{total}.
\item %
  Resolving a Prolog query results in a substitution that, when
  applied to the goal, produces a solution in the form of a term that
  can be derived from the given rules.  We extend our interpreter to
  also produce a trace of the applied rules, which enables it to
  produce a proof term that shows the resulting substitution is valid.
\item %
  We integrate this proof search algorithm with Agda's
  \emph{reflection} mechanism (Section~\ref{sec:reflection}). This
  enables us to \emph{quote} the type of a lemma we would like to
  prove, pass this term as the goal of our proof search algorithm, and
  finally, \emph{unquote} the resulting proof term, thereby proving
  the desired lemma.
\end{itemize}

Although Agda already has built-in proof search
functionality~\citep{lindblad}, our approach has several key
advantages over most existing approaches to proof automation:

\begin{itemize}
\item Our library is highly customizable. We may parametrize our
  tactics over the search depth, hint database, or search
  strategy. Each of these is itself a first-class Agda value, that may
  be inspected or transformed, depending on the user's needs.
\item Although we limit ourself in the paper to a simple depth-first
  search, different proofs may require a different search strategy. To
  illustrate this point, we will develop a variation of our tactic
  that limits the number of times certain rules may be applied
  (Section~\ref{sec:extensible}).
\item Users need not learn a new programming language to modify
  existing tactics or develop tactics of their own. They can use a
  full-blown programming language to define their tactics, rather than
  restrict themselves to a domain-specific tactic language such as
  Ltac.
\item Finally, users can use all the existing Agda technology for
  testing and debugging \emph{programs} when debugging the generation
  of \emph{proofs}. Debugging complex tactics in Coq requires a great
  deal of expertise -- we hope that implementing tactics as a library
  will make this process easier.
\end{itemize}

We will compare our library with the various alternative forms of
proof automation in greater depth in Section~\ref{sec:discussion},
after we have presented our development.

All the code described in this paper is freely available from
GitHub.\footnote{
  See \url{https://github.com/pepijnkokke/AutoInAgda}.
} It is important to emphasize that all our code
is written in the safe fragment of Agda: it does not depend on any
postulates or foreign functions; all definitions pass Agda's
termination checker; and all metavariables are resolved.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
