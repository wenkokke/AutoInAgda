## Auto In Agda

#### Abstract

> TODO: put abstract here

#### Technical Details

This repository contains the sources for the *[Auto In Agda](/AutoInAgda.pdf?raw=true)*.
The `paper` sub-directory contains the literate Agda files that make up the paper.
The `code` sub-directory contains the Agda source code.

Some notes:

  - the code was written for use with [version 0.7 of the Agda standard
    library](http://www.cse.chalmers.se/~nad/software/lib-0.7.tar.gz);

  - the code is released under an [MIT license](code/LICENSE);

  - the paper is compiled using [lhs2TeX](www.andres-loeh.de/lhs2tex/);

  - compilation of the paper is facilitated using a
    [rake](http://rake.rubyforge.org/) build script (call `rake paper`).
