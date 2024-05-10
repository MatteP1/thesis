# Compiling the Project

## Required Packages and Versions Known to Compile Project

To compile the project, make sure the following packages are installed.

- coq-core              8.19.0
- coq-iris              4.2.0
- coq-iris-heap-lang    4.2.0
- coq-stdlib            8.19.0
- coq-stdpp             1.10.0

Installation instructions can be found at [coq.inria.fr/download](https://coq.inria.fr/download) and [The Iris Repository](https://gitlab.mpi-sws.org/iris/iris/blob/master/README.md).

## Compilation instructions

Clone the repository and navigate to `/thesis`. To generate a make file, run:

	coq_makefile -f _CoqProject -o CoqMakefile

Then compile the project with:

	make -f CoqMakefile