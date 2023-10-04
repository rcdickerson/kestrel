#!/bin/bash

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./benchmarks/*)
else
  benchmark_dirs=("./benchmarks/$benchmark_group")
fi

alignment_base_dir="./results/log/alignment"
verification_base_dir="./results/log/verification"

output_file="./results_summary.data"
echo "Storing summary in $output_file"
echo "group, benchmark, a_unaligned, a_minloops, a_sa, v_unaligned, v_minloops, v_sa" > "$output_file"

for benchmark_group in "${benchmark_dirs[@]}"
do
  group_name=`basename $benchmark_group`
  for file in $benchmark_group/*.c
  do
      echo "$group_name," >> "$output_file"
      truncate -s-1 $output_file
      benchmark_name=`basename $file .c`
      echo "$benchmark_name," >> "$output_file"
      truncate -s-1 $output_file
      cat "$alignment_base_dir/$group_name/unaligned/$benchmark_name.log" | grep real | cut -f2 >> "$output_file"; truncate -s-1 $output_file; echo "," >> "$output_file"; truncate -s-1 $output_file
      cat "$alignment_base_dir/$group_name/count-loops/$benchmark_name.log" | grep real | cut -f2 >> "$output_file"; truncate -s-1 $output_file; echo "," >> "$output_file"; truncate -s-1 $output_file
      cat "$alignment_base_dir/$group_name/sa/$benchmark_name.log" | grep real | cut -f2 >> "$output_file"; truncate -s-1 $output_file; echo "," >> "$output_file"; truncate -s-1 $output_file
      cat "$verification_base_dir/$group_name/unaligned/$benchmark_name-una.log" | grep real | cut -f2 >> "$output_file"; truncate -s-1 $output_file; echo "," >> "$output_file"; truncate -s-1 $output_file
      cat "$verification_base_dir/$group_name/count-loops/$benchmark_name-cou.log" | grep real | cut -f2 >> "$output_file"; truncate -s-1 $output_file; echo "," >> "$output_file"; truncate -s-1 $output_file
      cat "$verification_base_dir/$group_name/sa/$benchmark_name-sa.log" | grep real | cut -f2 >> "$output_file"
  done
done
echo "Done"
