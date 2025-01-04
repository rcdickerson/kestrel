from datetime import datetime
import os
from pathlib import Path
import shutil
import subprocess
from tqdm import tqdm

BENCHMARK_DIR = './benchmarks/euf'
OUTPUT_ROOT_DIR = './results'
LOG_DIR_NAME = 'logs'
ALIGNMENT_DIR_NAME = 'alignments'
SUMMARY_FILE_NAME = 'summary.txt'
EXTRACTION_TECHNIQUES = ['unaligned', 'count-loops', 'sa']
KESTREL_BIN = './target/release/kestrel'
SA_MAX_ITERATIONS = 300000
TIMEOUT_SEC = 60 * 5

def run_benchmarks(output_dir):
  summary_file = os.path.join(output_dir, SUMMARY_FILE_NAME)
  for technique in EXTRACTION_TECHNIQUES:
    print(f"Running with technique: {technique}...")
    bench_count = sum(len(files) for _, _, files in os.walk(BENCHMARK_DIR))
    with tqdm(total=bench_count) as pbar:
      for root, dirs, files in os.walk(BENCHMARK_DIR):
        if len(files) == 0:
          continue
        log_dir = os.path.join(output_dir, LOG_DIR_NAME, technique, os.path.basename(root))
        align_dir = os.path.join(output_dir, ALIGNMENT_DIR_NAME, technique, os.path.basename(root))
        os.makedirs(log_dir, exist_ok=True)
        os.makedirs(align_dir, exist_ok=True)
        for name in files:
          benchmark = os.path.join(root, name)
          with open(os.path.join(log_dir, f"{Path(name).stem}.log"), 'w') as logfile:
              args = [KESTREL_BIN, \
                      '-i', benchmark, \
                      '-o', os.path.join(align_dir, f"{Path(name).stem}.dfy"), \
                      '--infer-invariants', \
                      '--output-mode', 'dafny', \
                      '--output-summary', summary_file, \
                      '--sa-max-iterations', str(SA_MAX_ITERATIONS), \
                      technique]
              try:
                subprocess.run(args,
                               stdout=logfile,
                               stderr=subprocess.STDOUT,
                               timeout=TIMEOUT_SEC)
              except subprocess.TimeoutExpired:
                with open(summary_file, 'a') as summary:
                  summary.write(f"{benchmark},{technique},TIMEOUT,false\n")
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
