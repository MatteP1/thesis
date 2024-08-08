# Compiling the Project

## Required Packages and Versions Known to Compile Project

To compile the project, make sure the following packages are installed.

- coq-core              8.19.0
- coq-iris              4.2.0
- coq-iris-heap-lang    4.2.0
- coq-stdlib            8.19.0
- coq-stdpp             1.10.0

Installation instructions can be found at [coq.inria.fr/download](https://coq.inria.fr/download) and [The Iris Repository](https://gitlab.mpi-sws.org/iris/iris/blob/master/README.md).

## Compilation Instructions

Clone the repository and navigate to `/thesis`. Running `make` here compiles the project; it will create a Coq Makefile for the project and immediately run it.

Alternatively, one can generate the Coq Makefile manually using the following command:

	coq_makefile -f _CoqProject -o CoqMakefile

The project is then compiled with:

	make -f CoqMakefile

Note that some of the files can take a while to compile.
