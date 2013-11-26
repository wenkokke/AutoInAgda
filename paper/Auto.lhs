\documentclass[preprint,authoryear]{sigplanconf}

\def\textmu{}
%include agda.fmt

\include{Preamble}
\usepackage{agda}
\begin{document}

\conferenceinfo{ICFP'14} {September 1--3, 2014, G\"oteborg, Sweden}

\title{Programming Proof Search}

\authorinfo{Pepijn Kokke \and Wouter Swierstra}
           {Universiteit Utrecht}
           {w.s.swierstra@@uu.nl}
\maketitle

\begin{abstract}
Lorem ipsum sic dolor amet\wouter{Hier moet de abstract komen}
\end{abstract}

\section{Introduction}
\label{sec:intro}

Writing proof terms in type theory is hard. Interactive proof
assistants based on type theory, such as Agda~\cite{agda} or
Coq~[\citeyear{coq}], take very different approaches to facilitating this
process.

Agda encourages proof automation through proof by
reflection~\cite{ulf-tphols}. In combinatior with Agda's reflection
mechanism~\cite{van-der-walt}, developers can write powerful automatic
decision procedures~\cite{allais}. Unfortunately, not all proofs are
easy to automate in this fashion. In that case, the user interacts
with the system to construct a proof term step-by-step. To discharge
the simple cases, \citet{lindblad} have hardwired a
first-order proof search algorithm into Agda's interactive development
environment.

Coq takes a very different approach. Besides the programming language
fragment Gallina, there is a separate tactic language Ltac.  Together
with several highly customizable tactics for proof search and
automation, Ltac can be used to simplify complex
proofs~\cite{chlipala}. Having to introduce a separate tactic
language, however, exposes limitations in expressivity of Gallina. It
seems at odds with the spirit of type theory, where a single language
is used for both proof and computation, to introduce a new language
for proof automation.

This paper tries to combine the best of both worlds by implementing
tactics for proof search \emph{within} Agda itself. More specifically,
this paper makes the following novel contributions:
\begin{itemize}
\item We show how to implement a Prolog interpreter in the style of
  \citet{stutterheim} in Agda (Section~\ref{sec:prolog}). Note that,
  in contrast to Agda, Prolog programs need not terminate. Using
  coinduction, however, we can write a \emph{total} interpreter for
  Prolog.
\item We extend this interpreter to not only produce the substitution
  that solves a Prolog goal, but also produces a proof tree
  (Section~\ref{sec:proofs}). This proof tree will serve as a witness
  for a proof found in this fashion.
\item We integrate this proof search algorithm with Agda's
  \emph{reflection} mechanism (Section~\ref{sec:reflection}. This
  enables us to quote the type of a goal, pass this to our
  Prolog-style interpreter, and unquote the resulting proof tree as a
  proof of our goal.
\item \todo{Example? Can we use our proof search to find out why a proof is
  not being found automatically?}
\end{itemize}


\section{Prolog in Agda}
\label{sec:prolog}

% \begin{code}\>\<%
% \>[0]\AgdaIndent{2}{}\<[2]%
% \>[2]\AgdaKeyword{data} \AgdaDatatype{Term} \AgdaSymbol{(}\AgdaBound{n} \AgdaSymbol{:} \AgdaDatatype{ℕ}\AgdaSymbol{)} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaKeyword{where}\<%
% \\
% \>[2]\AgdaIndent{4}{}\<[4]%
% \>[4]\AgdaInductiveConstructor{var} \AgdaSymbol{:} \AgdaDatatype{Fin} \AgdaBound{n} \AgdaSymbol{→} \AgdaDatatype{Term} \AgdaBound{n}\<%
% \\
% \>[2]\AgdaIndent{4}{}\<[4]%
% \>[4]\AgdaInductiveConstructor{con} \AgdaSymbol{:} \AgdaSymbol{∀} \AgdaSymbol{\{}\AgdaBound{k}\AgdaSymbol{\}} \AgdaSymbol{(}\AgdaBound{s} \AgdaSymbol{:} \AgdaBound{Name} \AgdaBound{k}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{ts} \AgdaSymbol{:} \AgdaDatatype{Vec} \AgdaSymbol{(}\AgdaDatatype{Term} \AgdaBound{n}\AgdaSymbol{)} \AgdaBound{k}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{Term} \AgdaBound{n}\<%
% \end{code}

% \begin{code}
%   data Term (n : ℕ) : Set where
%     var : Fin n → Term n
%     con : ∀ {k} (s : Name k) → (ts : Vec (Term n) k) → Term n
% \end{code}

% \begin{code}

%   data SearchTree (m : ℕ) : Set where
%     done : ∃₂ (λ δ n → Subst (m + δ) n) → SearchTree m
%     step : (∃ Rule → ∞ (SearchTree m)) → SearchTree m

% \end{code}

\section{Constructing proof trees}
\label{sec:proofs}

\section{Adding reflection}
\label{sec:reflection}

\section{Discussion}
\label{sec:discussion}

\todo{Mention Idris}

\bibliographystyle{plainnat}
\bibliography{Auto}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End:
