(TeX-add-style-hook "old_main"
 (lambda ()
    (LaTeX-add-bibliographies
     "main")
    (LaTeX-add-labels
     "sec:intro"
     "sec:motivation"
     "sec:prolog"
     "fig:injFig"
     "fig:fins"
     "sec:proofs"
     "sec:reflection"
     "sec:hintdbs"
     "sec:type-classes"
     "sec:discussion")
    (TeX-run-style-hooks
     "latex2e"
     "sigplanconf10"
     "sigplanconf"
     "preprint"
     "preamble")))

