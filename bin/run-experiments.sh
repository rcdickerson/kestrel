#!/bin/bash

# First argument: benchmark location
benchmark_dir=$1

# Second argument: extraction technique.
technique=$2

echo "Building KestRel"
cargo build --release
kestrel_exec=./target/release/kestrel

# Make the output and log directories
output_base_dir="./results"
output_dir="$output_base_dir/$technique"
log_dir="$output_base_dir/log/$technique"
echo "Storing results in $output_dir"
mkdir -p "$output_dir"
echo "Storing logs in in $log_dir"
mkdir -p "$log_dir"

for file in $benchmark_dir/*.c
do
  echo "$file..."
  file_basename=$(basename $file .c)

  output_file="$output_dir/$file_basename".c
  (time $kestrel_exec -i $file -o $output_file $technique) > "$log_dir/$file_basename".log 2>&1
done
echo "Done"
