#!/bin/bash

shopt -s nullglob

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./benchmarks/*)
else
  benchmark_dirs=("./benchmarks/$benchmark_group")
fi

# Second argument: extraction technique.
ext_technique=$2
if [ "$ext_technique" = "all" ]; then
  techniques=("unaligned" "count-loops" "sa")
else
  techniques=("$ext_technique")
fi

# Third argument: output mode.
out_mode=${3:-seahorn}

echo "Building KestRel"
cargo build --release
kestrel_exec=./target/release/kestrel

for group_dir in "${benchmark_dirs[@]}"
do
  group_name=`basename $group_dir`
  echo "Running $group_name benchmarks."

  for technique in "${techniques[@]}"
  do
    # Make the output and log directories
    output_base_dir="./results"
    output_dir="$output_base_dir/alignments/$out_mode/$group_name/$technique"
    log_dir="$output_base_dir/log/alignment/$out_mode/$group_name/$technique"
    echo "Storing results in $output_dir"
    mkdir -p "$output_dir"
    echo "Storing logs in in $log_dir"
    mkdir -p "$log_dir"

    # Run KestRel.
    for file in $group_dir/*.c
    do
        echo "$file..."
        file_basename=$(basename $file .c)

        if [ $out_mode == "dafny" ]; then
            output_file="$output_dir/$file_basename-${technique:0:3}".dfy
        else
            output_file="$output_dir/$file_basename-${technique:0:3}".c
        fi

        (time timeout 10m $kestrel_exec -i $file -o $output_file --output-mode=$out_mode $technique --sa-max-iterations=12000) > "$log_dir/$file_basename".log 2>&1
    done
  done
done
echo "Done"
