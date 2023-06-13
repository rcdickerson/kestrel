#!/bin/bash

shopt -s nullglob

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./results/chc/smt/*)
else
  benchmark_dirs=("./results/chc/smt/$benchmark_group")
fi

# Second argument: extraction technique.
ext_technique=$2
if [ "$ext_technique" = "all" ]; then
  techniques=("unaligned" "count-loops" "sa")
else
  techniques=("$ext_technique")
fi

# Output directory
output_base_dir="./results/freqhorn"

# FreqHorn executable.
freqhorn="../freqhorn/build/tools/deep/freqhorn"

for group_dir in "${benchmark_dirs[@]}"
do
  group_name=`basename $group_dir`
  echo "Verifying $group_name benchmarks with FreqHorn..."

  for technique in "${techniques[@]}"
  do
    # Make the log directory
    log_dir="$output_base_dir/log/$group_name/$technique"
    echo "Storing logs in in $log_dir"
    mkdir -p "$log_dir"

    # Run FreqHorn.
    for file in $group_dir/$technique/*.smt
    do
        echo "$file..."
        file_basename=$(basename $file .smt)
        (time timeout 10m $freqhorn $file) > "$log_dir/$file_basename".log 2>&1
    done
  done
done

echo "Done"
