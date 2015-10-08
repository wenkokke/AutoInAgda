## Auto In Agda

#### Abstract

> As proofs in type theory become increasingly complex, there is a
> growing need to provide better proof automation. This paper shows
> how to implement a Prolog-style resolution procedure in the
> dependently typed programming language Agda. Connecting this
> resolution procedure to Agda's reflection mechanism provides a
> first-class proof search tactic for first-order Agda
> terms. Furthermore, the same mechanism may be used in tandem with
> Agda's instance arguments to implement type classes in the style of
> Haskell. As a result, writing proof automation tactics need not be
> different from writing any other program.

#### Technical Details

This repository contains the sources for the
*[Auto In Agda](http://www.staff.science.uu.nl/~swier004/Publications/AutoInAgda.pdf)*.
The `paper` sub-directory contains the literate Agda files that make up the paper.
The `code` sub-directory contains the Agda source code.

Some notes:

  - the code was written for use with Agda 2.4.2 and [version 0.8.1 of the Agda standard
    library](https://github.com/agda/agda-stdlib/releases/tag/v0.8.1);

  - the code is released under an [MIT license](code/LICENSE);

  - the paper is compiled using [lhs2TeX](http://www.andres-loeh.de/lhs2tex/);

  - compilation of the paper is facilitated using a
    [rake](http://rake.rubyforge.org/) build script (call `rake paper`).
