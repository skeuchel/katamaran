[![CircleCI](https://img.shields.io/circleci/build/github/katamaran-project/katamaran)](https://app.circleci.com/pipelines/github/katamaran-project/katamaran)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran?ref=badge_shield)

Katamaran
=========

Katamaran is a verification framework for instruction set architectures in the
[Rocq proof assistant](https://rocq-prover.org/).
It provides the deeply-embedded language μSail, a variant
of the [Sail](https://github.com/rems-project/sail) language, for the
specification of instructions sets and provides furthermore facilities for the
specification of separation logic-based contracts and for semi-automatically
verifying these contracts. The goal is to formally specify and verify with
machine-checked proofs critical security guarantees of instruction sets. For
more information visit [our website](https://katamaran-project.github.io/).

Dependencies
------------

The development version of Katamaran is tested with Rocq 9.2 and 9.3 and has the following lower bounds:
```
rocq-core      >= 9.2
rocq-equations >= 1.3.2+9.2
rocq-iris      >= 4.5
rocq-stdpp     >= 1.13
```

### Using opam

An easy way to setup your system is to create a fresh opam switch, pin the Rocq and Iris versions and install equations (stdpp will be installed as a dependency of Iris):
```
opam switch create katamaran ocaml-base-compiler.5.2.1
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add rocq-core 9.2.0
opam pin add rocq-iris 4.5.0
opam pin add rocq-equations 1.3.2+9.2

```

### Using nix

The repository contains a flake.nix file that defines development shells that install all dependencies. To use it, you need to have [nix](https://nixos.org/download.html) installed. Then, you can enter a development shell with the following command:
```
nix develop
```
This will install all dependencies and open a shell with them available. Additionally it will set the COQPATH environment variable to include the dependencies. You can then compile the project within that shell or launch your favorite editor from within it.

There is also an `lsp` development shell with editor tooling: `nix develop .#lsp`. With [direnv](https://direnv.net/), `.envrc` loads the default shell; to load the `lsp` shell instead, create a `.envrc.local` containing `use flake .#lsp` (it is not committed).

Installation
------------

### Via opam (dev version)
Add our opam repository and install the latest development version from Github
with the following commands:
```
opam repo add katamaran https://github.com/katamaran-project/opam-repository.git
opam install coq-katamaran
```

### From github
```
git clone https://github.com/katamaran-project/katamaran.git
cd katamaran && make && make install
```

Alternatively, build with dune. `dune build` builds the library, the case
studies and the tests (which are not installed). Each part is a separate
package: `rocq-katamaran` (the library), `rocq-katamaran-minimalcaps`,
`rocq-katamaran-riscvpmp` and `rocq-katamaran-gvt`. For example:
```
dune build -p rocq-katamaran && dune install rocq-katamaran
```

Using
-----

The basic usage structure of Katamaran is described in the [USING.md](USING.md) file.
The easiest and recommended way to use the library for new developments is to adapt one of our existing case studies, for example the [MinimalCaps](case_study/MinimalCaps) machine.
Some more information about the internal structure of the library is provided in the [HACKING.md](HACKING.md) file.

License
-------
The Katamaran implementation is distributed under the 2-clause BSD license.

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2Fkatamaran-project%2Fkatamaran?ref=badge_large)
