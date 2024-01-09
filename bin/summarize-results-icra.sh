#!/bin/bash

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./benchmarks/*)
else
  benchmark_dirs=("./benchmarks/$benchmark_group")
fi

#alignment_base_dir="./results/log/alignment/icra"
#verification_base_dir="./results/log/verification/icra"
alignment_base_dir="./experiments/2023-11-13/log/alignment/icra"
verification_base_dir="./experiments/2023-11-13/log/verification/icra"

output_file="./results-summary-icra.data"
echo "Storing summary in $output_file"
echo "group, benchmark, a_unaligned, a_minloops, a_sa, v_unaligned, v_minloops, v_sa, v_unaligned_result, v_minloops_result, v_sa_result" > "$output_file"

no_newline() { perl -pi -e 'chomp if eof' $output_file; }
comma() { echo "," >> $output_file; no_newline; }

for benchmark_group in "${benchmark_dirs[@]}"
do
  group_name=`basename $benchmark_group`
  for file in $benchmark_group/*.c
  do
      echo "$group_name," >> $output_file; no_newline
      benchmark_name=`basename $file .c`
      echo "$benchmark_name," >> $output_file; no_newline
      cat "$alignment_base_dir/$group_name/unaligned/$benchmark_name.log" | grep real | cut -f2 >> $output_file; no_newline; comma
      cat "$alignment_base_dir/$group_name/count-loops/$benchmark_name.log" | grep real | cut -f2 >> $output_file; no_newline; comma
      cat "$alignment_base_dir/$group_name/sa/$benchmark_name.log" | grep real | cut -f2 >> $output_file; no_newline; comma
      cat "$verification_base_dir/$group_name/unaligned/$benchmark_name-una.log" | grep real | cut -f2 >> $output_file; no_newline; comma
      cat "$verification_base_dir/$group_name/count-loops/$benchmark_name-cou.log" | grep real | cut -f2 >> $output_file; no_newline; comma
      cat "$verification_base_dir/$group_name/sa/$benchmark_name-sa.log" | grep real | cut -f2 >> $output_file; no_newline; comma
      cat "$verification_base_dir/$group_name/unaligned/$benchmark_name-una.log" | grep "^Is SAT" >> $output_file; no_newline
      cat "$verification_base_dir/$group_name/unaligned/$benchmark_name-una.log" | grep "^Is not SAT" >> $output_file; no_newline; comma
      cat "$verification_base_dir/$group_name/count-loops/$benchmark_name-cou.log" | grep "^Is SAT" >> $output_file; no_newline
      cat "$verification_base_dir/$group_name/count-loops/$benchmark_name-cou.log" | grep "^Is not SAT" >> $output_file; no_newline; comma
      cat "$verification_base_dir/$group_name/sa/$benchmark_name-sa.log" | grep "^Is SAT" >> $output_file; no_newline
      cat "$verification_base_dir/$group_name/sa/$benchmark_name-sa.log" | grep "^Is not SAT" >> $output_file; no_newline
      echo "" >> $output_file
  done
done
echo "Done"
