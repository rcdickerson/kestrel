#!/bin/bash

shopt -s nullglob

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./results/alignments/*)
else
  benchmark_dirs=("./results/alignments/$benchmark_group")
fi

# Second argument: extraction technique.
ext_technique=$2
if [ "$ext_technique" = "all" ]; then
  techniques=("unaligned" "count-loops" "sa")
else
  techniques=("$ext_technique")
fi

# Output directory
output_base_dir="./results"

# Step 1: Compile to bytecode.
for group_dir in "${benchmark_dirs[@]}"
do
  group_name=`basename $group_dir`
  echo "Generating bytecode for $group_name benchmarks..."

  for technique in "${techniques[@]}"
  do
    # Make the output and log directories
    output_dir="$output_base_dir/chc/bytecode/$group_name/$technique"
    log_dir="$output_base_dir/log/chc/bytecode/$group_name/$technique"
    echo "Storing results in $output_dir"
    mkdir -p "$output_dir"
    echo "Storing logs in in $log_dir"
    mkdir -p "$log_dir"

    # Run SeaHorn.
    for file in $group_dir/$technique/*.c
    do
        echo "$file..."
        file_basename=$(basename $file .c)

        output_file="$output_dir/$file_basename".bc
        (time timeout 10m sea fe $file -o $output_file) > "$log_dir/$file_basename".log 2>&1
    done
  done
done


# Step 2: Generate SMT2

if [ "$benchmark_group" = "all" ]; then
  bytecode_dirs=($output_base_dir/chc/bytecode/*)
else
  bytecode_dirs=("$output_base_dir/chc/bytecode/$benchmark_group")
fi

for group_dir in "${bytecode_dirs[@]}"
do
  group_name=`basename $group_dir`
  echo "Generating SMT for $group_name benchmarks..."

  for technique in "${techniques[@]}"
  do
    # Make the output and log directories
    output_dir="$output_base_dir/chc/smt/$group_name/$technique"
    log_dir="$output_base_dir/log/chc/smt/$group_name/$technique"
    echo "Storing results in $output_dir"
    mkdir -p "$output_dir"
    echo "Storing logs in in $log_dir"
    mkdir -p "$log_dir"

    # Run SeaHorn.
    for file in $group_dir/$technique/*.bc
    do
        echo "$file..."
        file_basename=$(basename $file .bc)

        output_file="$output_dir/$file_basename".smt2
        (time timeout 10m sea horn $file -o $output_file) > "$log_dir/$file_basename".log 2>&1
    done
  done
done

echo "Done"
