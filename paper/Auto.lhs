\documentclass[natbib,preprint,authoryear]{sigplanconf}

\def\textmu{}
%include agda.fmt

\include{Preamble}

\begin{document}

\conferenceinfo{ICFP'14} {September 1--3, 2014, G\"oteborg, Sweden}

\title{Embedding Auto for Agda}

\authorinfo{Pepijn Kokke \and Wouter Swierstra}
           {Universiteit Utrecht}
           {w.s.swierstra@@uu.nl}
\maketitle

\begin{abstract}
Lorem ipsum sic dolor amet\wouter{Hier moet de abstract komen}
\end{abstract}

\section{Introduction}
\label{sec:intro}

Writing proofs in type theory is a lot of work. Coq provides a special
tactic language and proof search tactics. These are `hardwired' which
makes them less flexible. We show how to use Agda's reflection
mechanism to implement a customizable proof search tactic.

Specifically, this paper makes the following novel contributions:
\begin{itemize}
\item We show how to write a Prolog interpreter in the style of
  Stutterheim-Swierstra-Swierstra\todo{add citation} in Agda
  (Section~\ref{sec:prolog}). This is interesting as Prolog programs
  need not terminate; while Agda programs must be total. Using
  coinduction, however, we can write a total interpreter for Prolog;
\item We extend this interpreter to not only produce the substitution
  that solves a Prolog goal, but also produces a proof tree
  (Section~\ref{sec:proofs}). This proof tree can then be used as a
  witness for a proof found in this fashion.
\item We integrate this proof search algorithm with Agda's
  \emph{reflection} mechanism (Section~\ref{sec:reflection}. This
  enables us to quote the type of a goal, pass this to our
  Prolog-style interpreter, and unquote the resulting proof tree as a
  proof of our goal.
\end{itemize}

\todo{Example? Can we use our proof search to find out why a proof is
  not being found automatically?}

\section{Prolog in Agda}
\label{sec:prolog}

\wouter{Hier is een stukje code. Sommige Unicode herkent ie blijkbaar
  niet (zoals lambda's en delta's). De formatering is op zich
  makkelijk aan te passen met behulp van de
  \verb!\DeclareUnicodeCharacter! command. Zie de .lhs source voor een
  voorbeeld.}

 \DeclareUnicodeCharacter{948}{\ensuremath{\delta}}
 \DeclareUnicodeCharacter{955}{\ensuremath{\lambdaup}}
\begin{code}

  data SearchTree (m : ℕ) : Set where
    done : ∃₂ (λ δ n → Subst (m + δ) n) → SearchTree m
    step : (∃ Rule → ∞ (SearchTree m)) → SearchTree m

\end{code}

\section{Constructing proof trees}
\label{sec:proofs}

\section{Adding reflection}
\label{sec:reflection}

\section{Discussion}
\label{sec:discussion}

\bibliographystyle{plainnat}
\bibliography{Auto}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End:
