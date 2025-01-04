#KestRel

## Introduction

KestRel is a tool for automatically constructing aligned product
programs for relational verification. It uses e-graphs to represent a
space of possible product alignments between two programs, and finds
desirable product programs through a variety of configurable
extraction techniques. The generated product programs may then be
given to various off-the-shelf non-relational verifiers.

KestRel is written in [Rust](https://www.rust-lang.org/) and uses
[Cargo](https://doc.rust-lang.org/cargo/) to build. More information
on KestRel and its dependencies is available in [KestRel's README
file](https://github.com/rcdickerson/kestrel).

This archive contains:

+ This `overview.md` file.
+ `kestrel.tar.gz`, an archived Docker image for executing KestRel.
+ `kestrel`, a directory containing the source code and Coq
  formalization for KestRel.


## Hardware Dependencies

The full artifact can only be exercised on a Linux machine using an
x86-64 architecture. This is because KestRel uses the
[Kvasir](http://plse.cs.washington.edu/daikon/download/doc/daikon.html#Kvasir)
frontend to [Daikon](http://plse.cs.washington.edu/daikon) for loop
invariant inference; Kvasir documentation indicates it is only
supported on Linux running on x86-64.


## Getting Started Guide

This artifact is distributed as a [Docker](https://www.docker.com/) image.
To use it, you will need to install the Docker Engine as
described in the [official Docker installation
instructions](https://docs.docker.com/engine/install/). The image was
created and this guide was written using Docker 27.3.1, but any
contemporary Docker version is expected to work. On *nix systems,
running `sudo docker run hello-world` is a quick way to check that
Docker is installed and behaving correctly.

Once Docker Engine is installed, you need to load the KestRel
image in one of the following ways:

* If you have obtained the KestRel Docker image as a tar archive, you
  can load it directly:
  ```bash
  # docker load < kestrel.tar.gz
  ```

* You can pull the image from Docker Hub:
  ```bash
  # docker pull rcdickerson/kestrel:oopsla2025
  ```

* You can obtain the KestRel source code and build the Docker image
  yourself:
  ```bash
  $ git clone https://github.com/rcdickerson/kestrel.git
  $ cd kestrel
  # docker buildx build -t rcdickerson/kestrel:oopsla2025 .
  ```

After loading the KestRel image in one of these ways, you should
see it in the output of `docker images`, for example:

```bash
# docker images
REPOSITORY          TAG         IMAGE ID       CREATED         SIZE
rcdickerson/kestrel oopsla2025  c609df14739e   6 hours ago     9.73GB
```

### Running a Single Benchmark

Check that the KestRel image is running correctly by using it to run a
single benchmark. First, use `docker run` to launch a shell inside the
container:

``` bash
# docker run --rm -it --entrypoint bash rcdickerson/kestrel:oopsla2025
```

You should be in the `/kestrel` directory. KestRel should already
be built, but you can invoke `cargo` to be sure:

```bash
# cargo build --release
```

Run the `antonopolous/simple.c` benchmark:

```bash
./target/release/kestrel -i ./benchmarks/euf/antonopoulos/simple.c --infer-invariants
```

If you see some program output ending with a success message, then
KestRel is working.

```bash
...
KestRel completed in 2635ms
Verified: true
```


# Step-by-Step Instructions

All experiments run KestRel on some set of benchmarks with various
alignment strategies. KestRel supports three alignment techniques:

  1. `none`: naive concatenative alignment.
  2. `count-loops`: syntactic extraction which maximizes the number
     of fused loops.
  3. `sa`: semantic extraction using simulated annealing.

KestRel experiments attempt verification for each alignment, and logs,
alignments, and a summary file are all written to a
`/kestrel/results/<timestamp>` directory. It is advisable to mount
some external directory to the `/kestrel/results` path so that you can
access results outside of the container. To do this, first create a
directory outside of the container:

```bash
$ mkdir results
```
and then mount it with `-v` when entering the container:

``` bash
docker run --rm -it \
  -v ./results:/kestrel/results \
  --ulimit nofile=262144:262144 \
  --entrypoint bash \
  rcdickerson/kestrel:oopsla2025
```

Note also the `--ulimit nofile=262144:262144` to increased the file
descriptor limit. This is for the benefit of Daikon / Kvasir; without
this option, invariant inference may fail.

Once inside the container, you can use the scripts in the
`experiments` directory to reproduce the results in the paper. From
the `/kestrel` root directory, invoke experiment scripts with
`python3`:

- `python3 ./experiments/alignment-euf.py` runs all benchmarks in
  `benchmarks/euf` using Dafny as the backing verifier. This data is
  the source of the results in Table 1 and the graph in Figure 17 of
  the paper. On completion, the `results/<timestamp>` directory will
  contain logs and alignments, as well as a `summary.txt` CSV file
  lsiting verification results per benchmark. Rows of the summary file
  are formatted as: `benchmark location, extraction technique,
  verification time (ms), success (true) or failure (false)`
  Additionally, the `results/<timestamp>` directory will contain a
  `summary.tex` file depicting data from Table 1 and the Figure 17
  graph. The KestRel image does not contain a LaTeX distribution, but
  you can compile this file outside the container with your favorite
  LaTeX tool, e.g.: `pdflatex results/summary.tex`.

- `python3 ./experiments/ablation-extraction.py` runs an ablation
  study on extraction techniques to reproduce data depicted in Figure
  18 of the paper. On completion, the `results/<timestamp>` directory
  will contain three summary CSV files: `summary-syntactic.txt`,
  `summary-semantic.txt`, and `summary-combined.txt`. These
  respectively contain results using syntactic-only extraction,
  semantic-only extraction, and combined extraction. As before, rows
  of the summary files are formatted as: `benchmark location,
  extraction technique, verification time (ms), success (true) or
  failure (false)`

- `python3 ./experiments/ablation-cost.py` runs an ablation study on
  cost functions components and reproduces Figure 19 of the KestRel
  paper. On completion, the `results/<timestamp>` directory will
  contain three summary CSV files formatted as described above:
  `summary-runoff.txt`, `summary-fusion.txt`, and
  `summary-combined.txt`. These respectively contain the results using
  a cost function without loop fusion, a cost function without runoff
  counting, and the full cost function.

- `python3 ./experiments/alignment-array.py` runs all benchmarks in
  `benchmarks/array` using Seahorn as the backing verifier. This
  reproduces the results in Figure 20 of the KestRel paper. Upon
  completion, the `results/<timestamp>` directory will contain a
  `summary.txt` CSV file formatted as above, as well as a
  `summary.tex` file containing the result table as in Figure 20.

## Theory

The `theory` directory contains a Coq formalization of the CoreRel
calculus and its metatheory, as described in Sections 3 of the paper.
The Coq formalization is not intended to be exercised within the
KestRel container; the KestRel Docker image does not come bundled with
Coq. The `theory` directory may be found in this artifact archive
or on [Github](https://github.com/rcdickerson/kestrel/tree/main/theory).

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



# Reusability Guide

Using the existing KestRel verification pipeline requires annotating a
C file with a special block comment at the top. This comment has the
general form:

```
/* @KESTREL
 * pre: <condition>;
 * left: <function name>;
 * right: <function name>;
 * post: <condition>;
 */
```

For example, the `antonopolous/simple.c` KestRel input from
the `benchmarks/euf` looks like:

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

The `benchmarks` directory provides many more examples of KestRel
input files. See KestRel's README more more information on the input
format, including invariant hinting and providing test generators for
data-driven extraction.

KestRel execution is organized by workflows made of re-usable and
re-configurable task objects (see `src/workflow`). The main entry
point (`src/main.rs`) defines KestRel's current core workflow.
Extending the capabilities of KestRel can be accomplished by modifying
or create new workflows, or adding new tasks to the existing workflow,
while reusing functionality contained in existing task objects.
