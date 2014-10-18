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
library for proof search \emph{within} Agda itself. This has several
important advantages over the current approaches to proof automation:
you do not need to learn a new programming language to write new
tactics; you can use existing language technology to debug and test
your tactics; and wyou can use all of Agda's expressive power in the
design, implementation, and customization of tactics.  More
specifically, this paper makes the several novel contributions.

\begin{itemize}
\item %
  We show how to implement a Prolog interpreter in the style of
  \citet{stutterheim} in Agda (Section~\ref{sec:prolog}). Note that,
  in contrast to Agda, resolving a Prolog query need not terminate.
  Using coinduction, however, we can write an interpreter for Prolog
  that is \emph{total}. Furthermore, a Prolog query results in a
  substitution that, when applied to the goal, produces a solution in
  the form of a term that can be derived from the given rules.  Hence
  we need to ensure our interpreter also produces a proof term, that
  witnesses the validity of the resulting substitution.
\item %
  We integrate this proof search algorithm with Agda's
  \emph{reflection} mechanism (Section~\ref{sec:reflection}). This
  enables us to \emph{quote} the type of a lemma we would like to
  prove, pass this term as the goal of our proof search algorithm, and
  finally, \emph{unquote} the resulting proof term, thereby proving
  the desired lemma.
\item \todo{ We give awesome examples of our tactic in action.}
\end{itemize}

Although Agda already has built-in proof search
functionality~\citep{lindblad}, we believe that exploring the
first-class proof automation defined in this paper is still
worthwhile. We will discuss the advantages and disadvantages of
various forms of proof automation towards the end of this paper
(Section~\ref{sec:discussion}), after we have presented our work.

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
