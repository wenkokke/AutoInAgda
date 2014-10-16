\documentclass[preprint]{llncs}

%include agda.fmt
%include main.fmt
\include{preamble}

\begin{document}

\title{Auto in Agda}
\subtitle{Programming proof search using reflection}

\author{Pepijn Kokke\inst{1} \and Wouter Swierstra\inst{1}}

\institute{Universiteit Utrecht\\ \email{pepijn.kokke@@gmail \quad w.s.swierstra@@uu.nl}}

\maketitle

\begin{abstract}

  As proofs in type theory become increasingly complex, there is a
  growing need to provide better proof automation. This paper shows
  how to implement a Prolog-style resolution procedure in the
  dependently typed programming language Agda. Connecting this
  resolution procedure to Agda's reflection mechanism provides a
  first-class proof search tactic for first-order Agda
  terms. As a result, writing proof automation tactics need not be
  different from writing any other program.

\end{abstract}

%include intro.lagda
%include motivation.lagda
%include prolog.lagda
%include reflection.lagda
%%include typeclasses.lagda
%include discussion.lagda

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
