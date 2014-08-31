(TeX-add-style-hook "main"
 (lambda ()
    (LaTeX-add-bibliographies)
    (LaTeX-add-labels
     "sec:intro"
     "sec:motivation"
     "sec:prolog"
     "sec:reflection"
     "sec:type-classes"
     "sec:discussion")
    (TeX-run-style-hooks
     "latex2e"
     "sigplanconf10"
     "sigplanconf"
     "preprint"
     "preamble")))

