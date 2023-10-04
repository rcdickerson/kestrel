#!/bin/bash

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./benchmarks/*)
else
  benchmark_dirs=("./benchmarks/$benchmark_group")
fi

echo "Building KestRel"
cargo build
kestrel_exec=./target/debug/kestrel

output_file="./space_sizes.data"
echo "Storing results in $output_file"
> "$output_file"

for group_dir in "${benchmark_dirs[@]}"
do
  group_name=`basename $group_dir`
  echo "Counting $group_name..."

  # Run KestRel.
  for file in $group_dir/*.c
  do
      echo "$file..."
      echo "$file, " >> "$output_file"

      truncate -s-1 $output_file
      $kestrel_exec -i $file unaligned --space-size  | grep "Alignment space size" | cut -f4 -d" " >> "$output_file" 2>&1
  done
done
echo "Done"
