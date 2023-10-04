#!/bin/bash

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./benchmarks/*)
else
  benchmark_dirs=("./benchmarks/$benchmark_group")
fi

echo "Building KestRel"
cargo build --release
kestrel_exec=./target/release/kestrel

output_file="./sa_bench.data"
echo "Storing results in $output_file"
> "$output_file"

for group_dir in "${benchmark_dirs[@]}"
do
  group_name=`basename $group_dir`
  echo "Benchmarking $group_name..."

  # Run KestRel.
  for file in $group_dir/*.c
  do
      echo "$file..."
      echo "$file" >> "$output_file"

      # Do some low numbers first.
      for max_iter in 50 100 500
      do
          echo "$max_iter, " >> "$output_file"
          for i in {1..10}
          do
              truncate -s-1 $output_file
              (time timeout 10m $kestrel_exec -i $file sa --sa-max-iterations=$max_iter | grep "Best score" | cut -f3 -d" ") | sed 's/$/\,/' >> "$output_file" 2>&1
          done
      done

      # Then count by 1000 to 12000.
      for max_iter in {1000..12000..1000}
      do
          echo "$max_iter, " >> "$output_file"
          for i in {1..10}
          do
              truncate -s-1 $output_file
              (time timeout 10m $kestrel_exec -i $file sa --sa-max-iterations=$max_iter | grep "Best score" | cut -f3 -d" ") | sed 's/$/\,/' >> "$output_file" 2>&1
          done
      done
  done
done
echo "Done"
