#!/bin/bash

# First argument: benchmark group
benchmark_group=$1
benchmark_dir="./benchmarks/$benchmark_group"

# Second argument: extraction technique.
technique=$2

echo "Building KestRel"
cargo build --release
kestrel_exec=./target/release/kestrel

# Make the output and log directories
output_base_dir="./results"
output_dir="$output_base_dir/$benchmark_group/$technique"
log_dir="$output_base_dir/alignment_log/$benchmark_group/$technique"
echo "Storing results in $output_dir"
mkdir -p "$output_dir"
echo "Storing logs in in $log_dir"
mkdir -p "$log_dir"

# Run KestRel.
for file in $benchmark_dir/*.c
do
  echo "$file..."
  file_basename=$(basename $file .c)

  output_file="$output_dir/$file_basename".c
  (time timeout 5m $kestrel_exec -i $file -o $output_file $technique) > "$log_dir/$file_basename".log 2>&1
done
echo "Done"
