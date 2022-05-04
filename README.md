# SharpSAT-TD Preprocessor

This preprocessor is based on the preprocessor from [SharpSAT-TD](https://github.com/Laakeri/sharpsat-td), adapted to be used in [aspmc](https://github.com/raki123/aspmc) in the evaluation of Algebraic Answer Set Counting (AASC). There it is used for preprocessing of Algebraic Model Counting (AMC) instances.

# Compiling

The external dependencies needed are the [GMP library](https://gmplib.org/), the [MPFR library](https://www.mpfr.org/), and [CMAKE](https://cmake.org/).

To compile and link dynamically use

``./setupdev.sh``

To compile and link statically use

``./setupdev.sh static``


The binaries sharpSAT and flow_cutter_pace17 will be copied to the [bin/](https://github.com/Laakeri/sharpsat-td/tree/main/bin) directory.

# Running

The currently supported input/output formats are those of [Model counting competition 2021](https://mccompetition.org/assets/files/2021/competition2021.pdf).


Example preprocessing:

``./sharpSAT -m general -t FPVEGV <INPUT_FILE>``

Example preprocessing for idempotent semirings:

``./sharpSAT -m idemp -t FPVEGV <INPUT_FILE>``


## Flags

- `-m` - AASC evaluation mode; `general` for the general case of arbitrary semirings, `idemp` for the case of idempotent semirings
- `-t` - preprocessing tactics string (`F` FailedLiterals, `P` PropStren, `V` BackBone, `S` Sparsify, `E` MergeAdjEquivs, `G` EliminateDefSimplicial)
