import csv
from datetime import datetime
import os
from pathlib import Path
import shutil
import subprocess
from tqdm import tqdm

BENCHMARK_DIR = './benchmarks/elaenia'
OUTPUT_ROOT_DIR = './results-elaenia'
LOG_DIR_NAME = 'logs'
ALIGNMENT_DIR_NAME = 'alignments'
SUMMARY_FILE_NAME = 'summary.txt'
SUMMARY_LATEX_NAME = 'summary.tex'
EXTRACTION_TECHNIQUES = ['count-loops']
KESTREL_BIN = './target/release/kestrel'
SA_MAX_ITERATIONS = 30000
TIMEOUT_SEC = 20 # 60 * 5

def latex_cell(data):
  (time, success) = data
  if time == 'TIMEOUT':
    return time
  elif success:
    return "\\textcolor{DarkGreen}{\\ding{52}} " + f"({time} ms)"
  else:
    return "\\textcolor{red}{\\ding{54}} " + f"({time} ms)"

def write_latex(output_dir):
  # Failure / success data.
  names = set()
  naive = {}
  syntactic = {}
  semantic = {}
  with open(os.path.join(output_dir, SUMMARY_FILE_NAME), 'r') as summary_file:
    for row in csv.reader(summary_file):
      bench_name = Path(os.path.basename(row[0])).stem
      time = row[2]
      success = row[3] == "true"
      names.add(bench_name)
      if row[1] == 'unaligned':
        naive[bench_name] = (time, success)
      elif row[1] == 'count-loops':
        syntactic[bench_name] = (time, success)
      elif row[1] == 'sa':
        semantic[bench_name] = (time, success)
      else:
        raise ValueError(f"Unrecognized extraction technique: {row[1]}")

  # Per-task timing data.
  task_timings = {}
  for root, dirs, files in os.walk(BENCHMARK_DIR):
    if len(files) == 0:
      continue
    log_dir = os.path.join(output_dir, LOG_DIR_NAME, 'sa', os.path.basename(root))
    for name in files:
      if semantic[Path(name).stem][0] == 'TIMEOUT':
        continue
      with open(os.path.join(log_dir, f"{Path(name).stem}.log"), 'r') as logfile:
        lines = logfile.readlines()
        daikon_syn = lines[-11].split(':')[1].strip()
        houdini_syn = lines[-10].split(':')[1].strip()
        alignment = lines[-9].split(':')[1].strip()
        daikon_sem = lines[-7].split(':')[1].strip()
        houdini_sem = lines[-6].split(':')[1].strip()
        total = int(daikon_syn) + int(houdini_syn) + int(alignment) + int(daikon_sem) + int(houdini_sem)
        task_timings[Path(name).stem] = (daikon_syn, houdini_syn, alignment, daikon_sem, houdini_sem, total)
    names_by_timing = sorted(task_timings.keys(), key = lambda name: task_timings[name][5], reverse=True)

  with open(os.path.join(output_dir, SUMMARY_LATEX_NAME), 'w') as latex_file:
    latex_file.write("\\documentclass{article}\n" \
                     "\\usepackage{pifont}\n" \
                     "\\usepackage{tikz}\n" \
                     "\\usepackage{pgfplots}\n" \
                     "\\pgfplotsset{compat=newest}\n" \
                     "\\usepackage{xcolor}\n" \
                     "\\definecolor{DarkGreen}{HTML}{006400}\n" \
                     "\\begin{document}\n" \
                     "\\begin{tabular}{l|l|l|l}\n" \
                     "\\hline \n" \
                     "\\textbf{Benchmark} & \\textbf{Na\\\"{i}ve} & \\textbf{Syntactic} & \\textbf{Full} \\\\ \n" \
                     "\\hline\n")
    for name in sorted(names):
      latex_file.write(f"{name} & " \
                       f"{latex_cell(naive[name])} & " \
                       f"{latex_cell(syntactic[name])} & " \
                       f"{latex_cell(semantic[name])} \\\\ \n")
    latex_file.write("\\hline\n"
                     "\\end{tabular}\n"
                     "\\newpage\n")

    xticklabels = ','.join(names_by_timing)
    latex_file.write("\\begin{tikzpicture}\n" \
                     "\\begin{axis}[height=.3\\textheight, ybar stacked, ytick=data, xtick=data, " \
                     "ylabel={Time (s)}, ymin=0, x tick label style={rotate=45,anchor=east}, " \
                     "tick label style={font=\\scriptsize}, legend style={font=\\small}, " \
                     "label style={font=\\small}, axis y line*=none, axis x line*=bottom, " \
                     "width=.9\\textwidth, bar width=2mm, area legend," \
                     "xticklabels={" \
                     f"{xticklabels}" \
                     "}, " \
                     "symbolic x coords={" \
                     f"{xticklabels}" \
                     "}] \n")
    for i in range(0, 5):
      latex_file.write("\\addplot coordinates {")
      for name in names_by_timing:
        latex_file.write(f"({name},{int(task_timings[name][i]) / 1000})")
      latex_file.write("};\n")
    latex_file.write("\\legend{DaikonSyn, HoudiniSyn, Alignment, DaikonSem, HoudiniSem},\n" \
	             "\\end{axis}\n" \
                     "\\end{tikzpicture}\n")

    latex_file.write("\\end{document}")

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
                      '--spec-format', 'elaenia', \
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
  write_latex(output_dir)

if __name__ == "__main__":
    main()
