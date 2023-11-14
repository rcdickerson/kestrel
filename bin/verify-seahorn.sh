#!/bin/bash

shopt -s nullglob

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./results/alignments/seahorn/*)
else
  benchmark_dirs=("./results/alignments/seahorn/$benchmark_group")
fi

# Second argument: extraction technique.
ext_technique=$2
if [ "$ext_technique" = "all" ]; then
  techniques=("unaligned" "count-loops" "sa")
else
  techniques=("$ext_technique")
fi

for group_dir in "${benchmark_dirs[@]}"
do
  group_name=`basename $group_dir`
  echo "Verifying $group_name benchmarks."

  for technique in "${techniques[@]}"
  do
    input_dir="$group_dir/$technique"

    # Make the log directory
    log_dir="./results/log/verification/seahorn/$group_name/$technique"
    echo "Storing verification logs in in $log_dir"
    mkdir -p "$log_dir"

    # Run Seahorn.
    for file in $input_dir/*.c
    do
      echo "$file..."
      file_basename=$(basename $file .c)
      (time timeout 2m sea pf -m64 --horn-strictly-la=false $file) > "$log_dir/$file_basename".log 2>&1
    done
  done
done
echo "Done"
