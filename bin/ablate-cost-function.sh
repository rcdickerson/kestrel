#!/bin/bash

shopt -s nullglob

output_base_dir="./results/cost_ablation_study"
mkdir -p $output_base_dir

# First argument: benchmark group
benchmark_group=$1
if [ "$benchmark_group" = "all" ]; then
  benchmark_dirs=(./benchmarks/euf/*)
else
  benchmark_dirs=("./benchmarks/euf/$benchmark_group")
fi

# Second argument: output mode.
out_mode=${2:-dafny}

# The ablation study flags.
ablations=( "--af-relation-size" "--af-update-matching" "--af-loop-head-matching" "--af-loop-double-updates" "--af-loop-executions" "" )

echo "Building KestRel"
cargo build --release
kestrel_exec=./target/release/kestrel

summary_file="$output_base_dir/summary.csv"

for group_dir in "${benchmark_dirs[@]}"
do
  for ablation in "${ablations[@]}"
  do
    if [ "$ablation" = "" ]; then
        flag_desc="none"
    else
        flag_desc="$ablation"
    fi

    group_name=`basename $group_dir`
    echo "Running $group_name benchmarks with flag $flag_desc."
    echo "${flag_desc}" >> $summary_file

    # Make the output and log directories
    output_dir="$output_base_dir/alignments/$out_mode/$group_name"
    log_dir="$output_base_dir/log/alignment/$out_mode/$group_name"
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
            output_file="$output_dir/$file_basename-$ablation".dfy
        else
            output_file="$output_dir/$file_basename-$ablation".c
        fi

        (time timeout 5m $kestrel_exec --infer-invariants --output-summary $summary_file -i $file -o $output_file --output-mode=$out_mode sa --sa-start-random --sa-max-iterations=12000 $ablation) > "$log_dir/$file_basename".log 2>&1
    done
  done
done
echo "Done"
