(TeX-add-style-hook "main"
 (lambda ()
    (LaTeX-add-bibliographies)
    (TeX-run-style-hooks
     "latex2e"
     "sigplanconf10"
     "sigplanconf"
     "preprint"
     "preamble")))

