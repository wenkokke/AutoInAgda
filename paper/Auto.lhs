\documentclass[preprint]{sigplanconf}

\def\textmu{}
%include agda.fmt
\usepackage{agda}

\include{Preamble}


\begin{document}

\conferenceinfo{ICFP'14} {September 1--3, 2014, G\"oteborg, Sweden}

\title{Programming Proof Search}

\authorinfo{Pepijn Kokke \and Wouter Swierstra}
           {Universiteit Utrecht}
           {} %TODO: email address here
\maketitle

\begin{abstract}
Lorem ipsum sic dolor amet\wouter{Hier moet de abstract komen}
\end{abstract}

\section{Introduction}
\label{sec:intro}

Writing proof terms in type theory is hard. Interactive proof
assistants based on type theory, such as Agda~\cite{agda} or
Coq~\cite{coq}, take very different approaches to facilitating this
process.


The Coq proof assistant has two distinct language fragments.  Besides
the programming language Gallina, there is a separate tactic language
for writing and programming proof scripts.  Together with several
highly customizable tactics, the tactic language Ltac can provide
powerful proof automation~\cite{chlipala}. Having to introduce a
separate tactic language, however, exposes limitations in expressivity
of Gallina. It seems at odds with the spirit of type theory, where a
single language is used for both proof and computation, to introduce a
new language for proof automation. \todo{What is the drawback of
  having a separate tactic language?}


Agda does not have Coq's dichotomy of proof and programming
language. Instead, programmers are encouraged to automate proofs by
writing their own solvers~\cite{ulf-tphols}. In combinatior with
Agda's reflection mechanism~\cite{van-der-walt}, developers can write
powerful automatic decision procedures~\cite{allais}. Unfortunately,
not all proofs are easy to automate in this fashion. In that case, the
user interacts with the integrated development environment to
construct a proof term step-by-step. 

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

\section{Motivation}
\label{sec:motivation}

Before describing the \emph{implementation} of our library, we will
give a brief motivating example describing its \emph{use}.

We can define a predicate |Even| on natural numbers as follows:

\begin{code}
  data Even  : ℕ →  Set where
    Base  : Even 0
    Step : ∀ {n} → Even n → Even (suc (suc n))
\end{code}

Next we can prove properties of this definition:

\begin{code}
  evenSum : ∀ {n m} -> Even n -> Even m -> Even (n + m)
  evenSum Base e2 = e2
  evenSum (Step e1) e2 = Step (evenSum e1 e2)
\end{code}

To use this lemma, we need to explicitly call the lemma. For example:

\begin{code}
  simple : ∀ {n} → Even n → Even (n + 2)
  simple e =  evenSum e (Step Base)
\end{code}

This has its drawbacks. Constructing explicit proof objects in this
fashion is not easy. The proof is brittle. We cannot easily reuse it
to prove similar statements such as |Even (n + 4)|. If we need to
reformulate our statement slightly, proving |Even (2 + n)| instead, we
need to rewrite our proof. Proof automation could really help here.

In Coq, tactics such as |auto| can be customized to handle all these
examples. Using high-level tactics makes the proof more robust against
reformulations of the exact proof statement. This paper shows how to
implement such an |auto| tactic in Agda.

Instead we will assemble any lemmas useful in our domain in a hint
database:

\begin{code}
  hints : HintDB
  hints = hintdb  (quote Base 
                  :: quote Step 
                  :: quote evenSum 
                  :: [])
\end{code}

Next we use Agda's reflection mechanism to quote the goal that we are
trying to prove. The language construct |quoteGoal g in ...| binds the
type of the current goal to |g|; we then call a \emph{function}
|auto|, passing our hint database and goal as arguments. The auto
function tries to construct a proof term of type |Even n -> Even (n +
2)| from the hint database. If this is successful, we unquote the
proof term:

\begin{code}
  test : ∀ {n} → Even n → Even (n + 2)
  test = quoteGoal g in unquote (auto 5 hints g)
\end{code}
What happens if no proof exists?

\begin{code}
  test : ∀ {n} → Even n → Even (n + 1)
  test = quoteGoal g in unquote (auto 5 hints g)
\end{code}

This goes beyond what is currently possible using the Agsy proof
search. In particular, we can add hints to a database; customize the
search depth; or even the search strategy used.

Of course, such invocations of the |auto| function may fail. In that
case, the |auto| function generates a dummy term, whose type explains
that the search space has been exhausted. Unquoting this term, then
gives a type error message. For example, trying to prove |Even n ->
Even (n + 3)| in this style gives the following error:

\begin{verbatim}
    Err searchSpaceExhausted !=< 
     Even .n -> Even (.n + 3) of type Set
\end{verbatim}


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
