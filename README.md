# KestRel

KestRel is a tool for automatically constructing aligned product
programs for relational verification. It uses e-graphs to represent a
space of possible product alignments between two programs, and finds
desirable product programs through a variety of configurable
extraction techniques. The generated product programs may then be
given to various off-the-shelf non-relational verifiers.

## Dependencies

KestRel requires the following system libraries and utilites:

- [Clang](https://clang.llvm.org/) for C parsing and compiling.
- [Daikon](https://plse.cs.washington.edu/daikon/) for invariant
  detection, including the
  [Kvasir](http://plse.cs.washington.edu/daikon/download/doc/daikon.html#Kvasir)
  Daikon frontend for C. Note Kvasir is only supported on x86
  architectures.
- [Dafny](https://dafny.org/) for Houdini-style invariant inference
  and certain verification pipelines.
- [Java Runtime Environment](https://www.java.com) for running Daikon.
- [SeaHorn](https://seahorn.github.io/) for certain verification
  pipelines.

KestRel is written in [Rust](https://www.rust-lang.org/), and manages
its library dependencies with
[Cargo](https://doc.rust-lang.org/cargo/).

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

The `bin` directory contains various scripts for running KestRel
experiments.

- `bin/run-alignments.sh` runs outputs alignments for a group of
  benchmarks. It optionally takes three arguments: benchmark group,
  extraction techique, and output mode. For example,
  `bin/run-alignments.sh barthe count-loops dafny` runs all benchmarks
  in the `barthe` directory using `count-loops` extraction and outputs
  Dafny. The first and second argument default to `all`, which outputs
  alignments for each possibility. The third argument defaults to
  `seahorn` output.

- `bin/verify-seahorn.sh` runs SeaHorn on all alignments output by
  `bin/run-alignments.sh`. It is meant to be run from inside the
  SeaHorn Docker image.

## KestRel Input Format

Coming soon!

## Docker

Containerization of KestRel with its dependencies is available via a
[Docker](https://www.docker.com/) image.

### Downloading the Docker Image

Coming soon!

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
docker run -it --ulimit nofile=262144:262144 kestrel
```

(Note the increased file descriptor limit -- invariant inference may
fail without this.)

See the [docker run
documentation](https://docs.docker.com/reference/cli/docker/container/run/)
for more ways to use the image.
