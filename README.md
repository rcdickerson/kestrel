# KestRel

KestRel is a tool for automatically constructing aligned product
programs for relational verification. It uses e-graphs to represent a
space of possible product alignments between two programs, and finds
desirable product programs through a variety of configurable
extraction techniques. The generated product programs may then be
given to various off-the-shelf non-relational verifiers.

Work on KestRel appeared at 
[OOPSLA 2025](https://2025.splashcon.org/track/OOPSLA) 
[[pdf](https://robd.io/papers/kestrel.pdf)].

## Dependencies

KestRel requires the following system libraries and utilites:

- [Clang](https://clang.llvm.org/) for C parsing and compiling.
- [Daikon](https://plse.cs.washington.edu/daikon/) for invariant
  detection, including the
  [Kvasir](http://plse.cs.washington.edu/daikon/download/doc/daikon.html#Kvasir)
  Daikon frontend for C. Note Kvasir is only supported on Linux
  running on x86-64 architectures.
- [Java Runtime Environment](https://www.java.com) for running Daikon.
- [Dafny](https://dafny.org/) for certain invariant inference and
  verification pipelines.
- [SeaHorn](https://seahorn.github.io/) for certain verification
  pipelines.

KestRel is written in [Rust](https://www.rust-lang.org/), and manages
its library dependencies with
[Cargo](https://doc.rust-lang.org/cargo/). All dependencies are present
in KestRel's Docker image.

## Building KestRel

Build KestRel using [Cargo](https://doc.rust-lang.org/cargo/) from the
KestRel root directory:

``` bash
cargo build
```

## Running KestRel

You may use `cargo-run` to execute the verification pipeline on single
input files. For example, the following command runs loop counting
extraction on the `antonopoulous/simple.c` benchmark, outputting a
prodcut program suitable for verification with SeaHorn:

``` bash
cargo run -- --input benchmarks/antonopoulos/simple.c count-loops
```

To use simulated annealing based extraction, include invariant
inference, and output the product program in Dafny:
 ``` bash
cargo run -- --input benchmarks/antonopoulos/simple.c --infer-invariants --output-mode dafny sa
```

To see all available KestRel options, run KestRel with the `--help` flag:
``` bash
cargo run -- --help
```

Note you can also invoke the binary directly once it has been built by cargo:
``` bash
target/debug/kestrel --help
```

## Running Experiments

The `experiments` directory contains various scripts for running KestRel
experiments. All experiments run KestRel on some set of `benchmarks` with
three different alignment strategies:

  1. `none`: naive concatenative alignment.
  2. `count-loops`: syntactic extraction which maximizes the number
     of fused loops.
  3. `sa`: semantic extraction using simulated annealing.

Verification is attempted for each alignment, and logs, alignments,
and a summary file are all written to a `./results/<timestamp>`
directory.

When running experiments from within the Docker container, it is recommended to
mount the results directory to something that lives outside of the container
using `-v <some local directory>:/kestrel/results`:

``` bash
docker run \
  --rm \
  -v ./results/:/kestrel/results \
  -it \
  --ulimit nofile=262144:262144 \
  --entrypoint bash \
  kestrel
```

You can run the experiments as follows:

- `python3 ./experiments/alignment-euf.py` runs all benchmarks in
  `benchmarks/euf` using Dafny as the backing verifier. This reproduces
  the results in Table 1 of the KestRel paper.

- `python3 ./experiments/ablation-extraction.py` runs an ablation
  study on extraction techniques and reproduces Figure 18 of the
  KestRel paper.

- `python3 ./experiments/ablation-cost.py` runs an ablation
  study on cost functions components and reproduces Figure 19 of the
  KestRel paper.

- `python3 ./experiments/alignment-array.py` runs all benchmarks in
  `benchmarks/array` using Seahorn as the backing verifier. This reproduces
  the results in Figure 20 of the KestRel paper.


## KestRel Input Format

KestRel input consists of a C file specially annotated with relational
pre- and post-conditions.

Currently, KestRel only supports a subset of C; it does not support
structs, and expects all iteration to be expressed as while loops.
Easing these restrictions is on the roadmap for future KestRel work.

The KestRel annotation is a special comment block that must appear
at the top of the input file. Its general form is:

```
/* @KESTREL
 * pre: <condition>;
 * left: <function name>;
 * right: <function name>;
 * post: <condition>;
 */
```

Conditions are expressed standard C-style boolean conditionals, with
references to variables in the left and right executions prefixed with
`left.` and `right.`, respectively. The `left` and `right` function
names may refer to either the same or different function definitions
contained in the input file.

Invariant hints can be given to KestRel by calling a dummy
`_invariant` function at the beginning of the loop body, passing a
condition as a string. References to variables in the left and right
executions should be prefixed with `l_` and `r_`, respectively. (It is
on the roadmap to make this naming consistent with the `left.` and
`right.` convention usesd in the file header.)

When performing data-driven extraction, KestRel uses a set of randomly
generated test inputs. Generated test inputs which do not meet the
relational precondition are discarded until a sufficient number of
inputs are discovered. To ensure randomly generated inputs always meet
some precondition (e.g., input values in two executions are always
equal), you may define a special test generator function called
`_test_gen(...)`. Inputs to this function are randomly generated by
KestRel, and the function may perform whatever operations are
neccessary to guarantee preconditions before calling
`_main(<lhs arguments>, <rhs_arguments>)`.

For example, here is the `antonopolous/simple.c` KestRel input from
the `benchmarks/euf` directory:

```
/* @KESTREL
 * pre:   left.n == right.n;
 * left:  fun;
 * right: fun;
 * post:  left.x == right.x;
 */

void _test_gen(int n) {
  n = n % 100;
  _main(n, n);
}

void fun(int n) {
  int x = 0;
  int i = 0;

  while( i <= n ) {
    _invariant("l_x == r_x");
    x = x + 1;
    i = i + 1;
  }
}
```

See the `benchmarks` directory for more examples of KestRel input.

## Docker

Containerization of KestRel with its dependencies is available via a
[Docker](https://www.docker.com/) image.

### Building the Docker Image

To build the docker image from scratch, first make sure you have the
following dependencies installed:
- [Docker](https://docs.docker.com/engine/install/)
- [BuildX](https://docs.docker.com/build/architecture/#install-buildx).
  This likely comes with modern Docker client installations. You can
  check by running `docker buildx` and verifying you see a usage help
  message. Building KestRel via the deprecated `docker build` may also
  work, but has not been explicitly tested.

To build the KestRel image, run the following command in the KestRel
root directory:

``` bash
docker buildx build -t kestrel .
```

### Running the Docker Image

Once the image exists on your machine, you may run an interactive
shell by saying:

``` bash
docker run --rm -it --ulimit nofile=262144:262144 --entrypoint bash kestrel
```

(Note the increased file descriptor limit -- invariant inference may
fail without this.)

See the [docker run
documentation](https://docs.docker.com/reference/cli/docker/container/run/)
for more ways to use the image.

## Code Structure and Documentation

You can generate
[rustdoc](https://doc.rust-lang.org/rustdoc/index.html) for KestRel
with cargo:

``` bash
cargo doc
```

Documentation will be written to `target/doc/kestrel`.

KestRel execution is organized according to workflows (see
`src/workflow`), sequences of reusable, configurable tasks. KestRel's
main workflow objects are constructed in `src/main.rs`. Future
development within or using KestRel should define new corresponding
workflows.

The top-level modules in the root `src` directory are as follows:

| Module Name | Description                                                      |
| ----------- | ---------------------------------------------------------------- |
| anneal      | Simulated annealing for semantic e-graph extraction.             |
| crel        | A C-like intermediate language supporting relational groupings.  |
| daikon      | Utilities for using Daikon to produce candidate loop invariants. |
| eggroll     | A lisp-like intermediate language defined for use with Egg.      |
| names       | Utilities for working with names in program syntax.              |
| output_mode | Configuration for KestRel’s supported output modes.              |
| shanty      | A utility for constructing C program syntax.                     |
| spec        | The specification language used throughout KestRel.              |
| syrtos      | A utility for constructing C program syntax.                     |
| unaligned   | Representation of unaligned programs given as input to KestRel.  |
| workflow    | Task organization for KestRel verification pipelines.            |

## Theory

The `theory` directory contains a Coq formalization of the CoreRel
calculus and its metatheory, as described in Sections 3 of the paper.

### Requirements

- `coq` (8.19.2, although other versions may also work)
- `coq-stdpp` (>= 1.11.0)

The easiest way to install `coq-stdpp` is via opam:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-stdpp
```

### Building

Run `make` in the `theory` directory.

### Key Definitions

| Definition  / Theorem            | Paper             | File                 | Name                    |
| -------------------------------- | ----------------- | -------------------- | ----------------------- |
| Imp Syntax                       | Figure 10         | IMP/Syntax.v         | `com`                   |
| Imp Semantics                    |                   | IMP/Semantics.v      | `ceval`                 |
| CoreRel Syntax                   | Figure 10         | CoreRel/Syntax.v     | `algn_com`              |
| CoreRel Semantics                | Figure 11         | CoreRel/Semantics.v  | `aceval`                |
| Embedding is Sound               | Theorem 3.2       | CoreRel/Embed.v      | `embed_is_iso`          |
| Reification of CoreRel           | Figure 12         | CoreRel/Embed.v      | `reify_com`             |
| Alignment Equivalence            | Definition 3.3    | CoreRel/Equiv.v      | `align_eqv`             |
| Reification preserves Eqivalence | Theorem 3.4       | CoreRel/Equiv.v      | `reify_preserves_eqv`   |
| Soundness of Product Program     | Corollary 3.5     | CoreRel/Equiv.v      | `product_program_sound` |
| CoreRel Realignment Laws         | Figure 13         | CoreRel/Equiv.v      | `whileR_unroll`, etc.   |
| Stuttered Loop Example           | Figure 3          | CoreRel/Examples.v   | `paper_example1_eqv`    |
