\documentclass[preprint]{sigplanconf}

%include agda.fmt
%include main.fmt
\include{preamble}

\begin{document}

\conferenceinfo{CPP'15} {January 12--14, 2015, Mumbai, India}
\titlebanner{Under preparation for CPP 2015}

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
