from datetime import datetime
import os
from pathlib import Path
import shutil
import subprocess
from tqdm import tqdm

BENCHMARK_DIR = './benchmarks/array'
OUTPUT_ROOT_DIR = './results'
LOG_DIR_NAME = 'logs'
ALIGNMENT_DIR_NAME = 'alignments'
SUMMARY_FILE_NAME = 'summary.txt'
EXTRACTION_TECHNIQUES = ['sa'] #['unaligned', 'count-loops', 'sa']
KESTREL_BIN = './target/release/kestrel'
SEAHORN_BIN = 'sea'
SA_MAX_ITERATIONS = 12000
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
          alignment_file = os.path.join(align_dir, f"{Path(name).stem}.c")

          start = datetime.now()

          # Step 1: Get an alignment from KestRel.
          with open(os.path.join(log_dir, f"{Path(name).stem}-alignment.log"), 'w') as logfile:
            try:
                args = [KESTREL_BIN, \
                        '-i', benchmark, \
                        '-o', alignment_file, \
                        '--output-mode', 'seahorn', \
                        '--sa-max-iterations', str(SA_MAX_ITERATIONS), \
                        technique]
                subprocess.run(args,
                               stdout=logfile,
                               stderr=subprocess.STDOUT,
                               timeout=TIMEOUT_SEC)
            except subprocess.TimeoutExpired:
                with open(summary_file, 'a') as summary:
                  summary.write(f"{benchmark},{technique},TIMEOUT,false\n")
                pbar.update(1)
                continue

          # Step 2: Ask Seahorn to verify.
          with open(os.path.join(log_dir, f"{Path(name).stem}-seahorn.log"), 'w') as logfile:
            try:
                args = ['docker', 'run', \
                        '-v', './results/:/home/usea/results', \
                        '-it', 'seahorn/seahorn-llvm14:nightly', \
                        SEAHORN_BIN, \
                        'pf', \
                        '-m64', \
                        '--horn-strictly-la=false', \
                        alignment_file]
                result = subprocess.run(args,
                                        stdout=logfile,
                                        stderr=subprocess.STDOUT,
                                        timeout=TIMEOUT_SEC)
                end = datetime.now()
                with open(summary_file, 'a') as summary:
                  if result.returncode == 0:
                    summary.write(f"{benchmark},{technique},{(end - start).microseconds * 1000},true\n")
                  else:
                    summary.write(f"{benchmark},{technique},{(end - start).microseconds * 1000},false\n")

            except subprocess.TimeoutExpired:
                with open(summary_file, 'a') as summary:
                  summary.write(f"{benchmark},{technique},TIMEOUT,false\n")
                pbar.update(1)
                continue

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
