from datetime import datetime
import os
from pathlib import Path
import shutil
import subprocess
from tqdm import tqdm

BENCHMARKS = ['./benchmarks/euf/unno/double-square.c', \
              './benchmarks/euf/barthe/loop-alignment.c', \
              './benchmarks/euf/barthe/loop-pipelining.c', \
              './benchmarks/euf/barthe/unroll.c', \
              './benchmarks/euf/antonopoulos/shemer.c']
OUTPUT_ROOT_DIR = './results'
LOG_DIR_NAME = 'logs'
ALIGNMENT_DIR_NAME = 'alignments'
SUMMARY_FILE_NAME = 'summary.txt'
ABLATIONS = [('runoff', ['--af-fusion', 'sa']), \
             ('fusion', ['--af-runoffs', 'sa']), \
             ('combined', ['sa'])]
KESTREL_BIN = './target/release/kestrel'
SA_MAX_ITERATIONS = 30000
TIMEOUT_SEC = 60 * 5

def run_benchmarks(output_dir):
  for (ablation_name, ablation_args) in ABLATIONS:
    print(f"Running ablation: {ablation_name}...")
    summary_file = os.path.join(output_dir, f"summary-{ablation_name}.txt")
    bench_count = len(BENCHMARKS)
    with tqdm(total=bench_count) as pbar:
      for benchmark in BENCHMARKS:
        log_dir = os.path.join(output_dir, LOG_DIR_NAME, ablation_name)
        align_dir = os.path.join(output_dir, ALIGNMENT_DIR_NAME, ablation_name)
        os.makedirs(log_dir, exist_ok=True)
        os.makedirs(align_dir, exist_ok=True)
        with open(os.path.join(log_dir, f"{Path(os.path.basename(benchmark)).stem}.log"), 'w') as logfile:
          try:
            args = [KESTREL_BIN, \
                    '-i', benchmark, \
                    '-o', os.path.join(align_dir, f"{Path(os.path.basename(benchmark)).stem}.dfy"), \
                    '--infer-invariants', \
                    '--output-mode', 'dafny', \
                    '--output-summary', summary_file, \
                    '--sa-max-iterations', str(SA_MAX_ITERATIONS)] + ablation_args
            subprocess.run(args,
                           stdout=logfile,
                           stderr=subprocess.STDOUT,
                           timeout=TIMEOUT_SEC)
          except subprocess.TimeoutExpired:
            with open(summary_file, 'a') as summary:
              summary.write(f"{benchmark},{ablation_name},TIMEOUT,false\n")
          pbar.update(1)

def main():
  print("Building KestRel...")
  build_result = subprocess.run(['cargo', 'build', '--release'])
  if build_result.returncode != 0:
    print("KestRel build failed!")
    return
  output_dir = os.path.join(OUTPUT_ROOT_DIR,
                            datetime.now().strftime('%Y_%m_%d-%H_%M_%S'))
  Path(output_dir).mkdir(parents=True, exist_ok=True)
  run_benchmarks(output_dir)

if __name__ == "__main__":
    main()
