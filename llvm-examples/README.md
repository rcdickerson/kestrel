# LLVM examples

Each subdirectory is a self-contained KestRel example that checks a Rust implementation against a C reference. The majority of examples came from the benchmarks folder, these examples contain a copy of the original file in their folder. When adding new test cases based on existing code, please include a copy of the original file the code is from.

## Layout of one example

```
<name>/
  <name>.c      the source C
  left.c        the reference C implementation
  right.rs      the Rust implementation
  spec.txt      the @KESTREL relational spec
  command.txt   the command to run this example
  notes.txt     this example's spec modifications and verification result
  output/       
      right_rust.ll             LLVM IR compiled from `right.rs`
      right_rust_scrubbed.ll    LLVM IR with Rellic-unfriendly attributes stripped
      right_rellic.c            Resulting LLVM IR to C by Rellic
      right_rellic_scrubbed.c   Lifted C with crel-unfriendly attributes stripped
      unaligned_product.c       left and right post pipeline combined but unaligned 
      aligned_product.c         the final aligned product program
```


## Running the examples

To run a single example, open `command.txt` and copy the command. All commands follow this skeleton:

``` bash
cargo run -- --left llvm-examples/<name>/left.c \
             --right llvm-examples/<name>/right.rs \
             --spec llvm-examples/<name>/spec.txt \
             count-loops --output-mode seahorn \
             --is-rust --verbose --infer-invariants
```

## Reading a SeaHorn result

- `Verified: true` — the verifier proved the postcondition.
- `Verified: false`, with a bare `sat` line printed — a counterexample
  exists, so the programs disagree or the spec doesn't hold.
- `Verified: false`, no `sat`, and the log contains `no assertion was found`
  — the spec's assertion never reached the solver. 

Some examples never reach a meaningful seahorn verdict. When that happens, the affected example's notes has a copy of the error.