# Boolean games

[![DOI](https://zenodo.org/badge/141577629.svg)](https://zenodo.org/badge/latestdoi/141577629)

The **BoolGames** library for the Coq proof assistant gathers a formalisation of Boolean games with random formulas as payoff functions.

## Dependencies

The **BoolGames** library depends on the following tools and libraries:

- [Coq](https://coq.inria.fr/)
- [MathComp](https://math-comp.github.io/math-comp)
- [Infotheo](https://staff.aist.go.jp/reynald.affeldt/shannon/)

It has been tested with Coq 8.8.0, MathComp 1.7.0, and Infotheo ae83217.

## Installation instructions

Coq and MathComp can be installed with [OPAM](https://opam.ocaml.org).

(They can also be downloaded, compiled and installed manually by
following the installation instructions on https://coq.inria.fr and
https://math-comp.github.io/math-comp)

Once OPAM is installed, type

```
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install coq.8.8.0 coq-mathcomp-character.1.7.0
```

When this installation step is completed, compile and install Infotheo
from the external directory:

```
$ cd external/infotheo
$ coq_makefile -f _CoqProject -o Makefile && make -j2 && make install
```

Then, you should just have to type the following in the root directory
containing this README.md:

```
$ ./configure && make -j2 && make install
```

## Documentation

To generate documentation from the Coq code using coqdoc and
[Graphviz](https://www.graphviz.org/), do:

    $ make doc

The documentation can then be browsed from html/toc.html with
your favorite browser.

## License

Given its dependencies:

- Coq (distributed under the LGPLv2.1 license)
- MathComp (distributed under the CeCILL-B license)
- Infotheo (distributed under the GPLv3 license)
- [coqgraph.ml](./coqgraph.ml) (distributed under the GPLv3 license)

the **BoolGames** library is distributed under the [GPLv3](./LICENSE) license.

## Authors

It was developed by [Erik Martin-Dorel](https://github.com/erikmd),
with advice from Sergei Soloviev.
