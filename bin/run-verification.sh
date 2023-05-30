#!/bin/bash

# First argument: benchmark group
benchmark_group=$1

# Second argument: technique
technique=$2

input_dir="./results/$benchmark_group/$technique"

# Make the log directory
log_dir="./results/verification_log/$benchmark_group/$technique"
echo "Storing verification logs in in $log_dir"
mkdir -p "$log_dir"

# Run Seahorn.
for file in $input_dir/*.c
do
  echo "$file..."
  file_basename=$(basename $file .c)
  (time timeout 10m sea pf -m64 $file) > "$log_dir/$file_basename".log 2>&1
done
echo "Done"
