"""
Copyright 2019 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Regression script for RISC-V random instruction generator
"""

import argparse
import os
import subprocess
import re
import sys
import logging

from datetime import date
from scripts.lib import *
from scripts.spike_log_to_trace_csv import *
from scripts.ovpsim_log_to_trace_csv import *
from scripts.sail_log_to_trace_csv import *

LOGGER = logging.getLogger()

def collect_cov(log_dir, out, iss, testlist, batch_size, lsf_cmd, steps, opts, timeout, si):
  """Collect functional coverage from the instruction trace

  Args:
    log_dir    : ISS log directory
    out        : Output directory
    iss        : Instruction set simulator
    test_list  : Testlist of the coverage test
    batch_size : Number of trace CSV to process per test
    lsf_cmd    : LSF command used to run the instruction generator
    steps      : csv:log to CSV, cov:sample coverage
    opts       : Additional options to the instruction generator
    timeout    : Timeout limit in seconds
    si         : Simulator used to run
  """
  log_list = []
  csv_list = []
  trace_log = ("%s/%s_trace_log" % (out, iss))
  logging.info("Processing trace log under %s" % log_dir)
  run_cmd("find %s -name \"*.log\" | sort > %s" % (log_dir, trace_log))
  with open(trace_log) as f:
    for line in f:
      line = line.rstrip()
      log_list.append(line)
      csv = line[0:-4] + ".csv"
      csv_list.append(csv)
  if steps == "all" or re.match("csv", steps):
    for i in range(len(log_list)):
      log = log_list[i]
      csv = csv_list[i]
      logging.info("Process %0s log[%0d/%0d] : %s" % (iss, i+1, len(log_list), log))
      if iss == "spike":
        process_spike_sim_log(log, csv, 1)
      else:
        logging.error("Full trace for %s is not supported yet" % iss)
        sys.exit(1)
  if steps == "all" or re.match("cov", steps):
    build_cmd = ("python3 run.py -si %s --co -o %s --cov -tl %s %s" %
                 (si, out, testlist, opts))
    base_sim_cmd = ("python3 run.py -si %s --so -o %s --cov -tl %s %s "
                    "-tn riscv_instr_cov_test --steps gen --sim_opts \"<trace_csv_opts>\"" %
                    (si, out, testlist, opts))
    logging.info("Building the coverage collection framework")
    run_cmd(build_cmd)
    file_idx = 0
    trace_idx = 0
    trace_csv_opts = ""
    batch_cnt = 1
    sim_cmd_list = []
    logging.info("Collecting functional coverage from %0d trace CSV" % len(csv_list))
    if batch_size > 0:
      batch_cnt = (len(csv_list)+batch_size-1)/batch_size;
      logging.info("Batch size: %0d, Batch cnt:%0d" % (batch_size, batch_cnt))
    for i in range(len(csv_list)):
      if batch_size > 0:
        file_idx = i / batch_size;
        trace_idx = i % batch_size;
      else:
        file_idx = 0
        trace_idx = i
      trace_csv_opts += (" +trace_csv_%0d=%s" % (trace_idx, csv_list[i]))
      if ((i == len(csv_list)-1) or ((batch_size > 0) and (trace_idx == batch_size-1))):
        sim_cmd = base_sim_cmd.replace("<trace_csv_opts>", trace_csv_opts)
        sim_cmd += ("  --log_suffix _%d" % file_idx)
        if lsf_cmd == "":
          logging.info("Processing batch %0d/%0d" % (file_idx+1, batch_cnt))
          run_cmd(sim_cmd)
        else:
          sim_cmd += (" --lsf_cmd \"%s\"" % lsf_cmd)
          sim_cmd_list.append(sim_cmd)
        trace_csv_opts = ""
    if lsf_cmd != "":
      run_parallel_cmd(sim_cmd_list, timeout)
    logging.info("Collecting functional coverage from %0d trace CSV...done" % len(csv_list))


def run_cov_debug_test(out, instr_cnt, testlist, batch_size, opts, lsf_cmd, timeout, si):
  """Collect functional coverage from the instruction trace

  Args:
    out        : Output directory
    instr_cnt  : Number of instruction to randomize
    test_list  : Testlist of the coverage test
    batch_size : Number of trace CSV to process per test
    lsf_cmd    : LSF command used to run the instruction generator
    opts       : Additional options to the instruction generator
    timeout    : Timeout limit in seconds
    si         : Simulator used to run
  """
  sim_cmd_list = []
  logging.info("Building the coverage collection framework")
  build_cmd = ("python3 run.py -si %s --co -o %s --cov -tl %s %s" %
               (si, out, testlist, opts))
  run_cmd(build_cmd)
  base_sim_cmd = ("python3 run.py -si %s --so -o %s --cov -tl %s %s "
                  "-tn riscv_instr_cov_debug_test --steps gen "
                  "--sim_opts \"+num_of_iterations=<instr_cnt>\"" %
                  (si, out, testlist, opts))
  if batch_size > 0:
    batch_cnt = int((instr_cnt+batch_size-1)/batch_size)
    logging.info("Batch size: %0d, Batch cnt:%0d" % (batch_size, batch_cnt))
  else:
    batch_cnt = 1
  logging.info("Randomizing %0d instructions in %0d batches", instr_cnt, batch_cnt)
  for i in range(batch_cnt):
    if batch_size > 0:
      if i == batch_cnt - 1:
        batch_instr_cnt = instr_cnt - batch_size * (batch_cnt - 1)
      else:
        batch_instr_cnt = batch_size
    else:
      batch_instr_cnt = instr_cnt
    sim_cmd = base_sim_cmd.replace("<instr_cnt>", str(batch_instr_cnt))
    sim_cmd += ("  --log_suffix _%d" % i)
    if lsf_cmd == "":
      logging.info("Running batch %0d/%0d" % (i+1, batch_cnt))
      run_cmd(sim_cmd)
    else:
      sim_cmd += (" --lsf_cmd \"%s\"" % lsf_cmd)
      sim_cmd_list.append(sim_cmd)
  if lsf_cmd != "":
    run_parallel_cmd(sim_cmd_list, timeout)
  logging.info("Collecting functional coverage from %0d random instructions...done" % instr_cnt)


def setup_parser():
  """Create a command line parser.

  Returns: The created parser.
  """
  # Parse input arguments
  parser = argparse.ArgumentParser()
  parser.add_argument("-o", "--output", type=str,
                      help="Output directory name", dest="o")
  parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                      help="Verbose logging")
  parser.add_argument("--dir", type=str,
                      help="Directory of ISS  log")
  parser.add_argument("-bz", "--batch_size", dest="batch_size", type=int, default=0,
                      help="Number of CSV to process per run")
  parser.add_argument("-d", "--debug_mode", dest="debug_mode", action="store_true",
                      help="Debug mode, randomize and sample the coverage directly")
  parser.add_argument("-i", "--instr_cnt", dest="instr_cnt", type=int, default=0,
                      help="Random instruction count for debug mode")
  parser.add_argument("-to", "--timeout", dest="timeout", type=int, default=1000,
                      help="Number of CSV to process per run")
  parser.add_argument("-s", "--steps", type=str, default="all",
                      help="Run steps: csv,cov", dest="steps")
  parser.add_argument("--iss", type=str, default="spike",
                      help="RISC-V instruction set simulator: spike,ovpsim,sail")
  parser.add_argument("-tl", "--testlist", type=str, default="",
                      help="Regression testlist", dest="testlist")
  parser.add_argument("--opts", type=str, default="",
                      help="Additional options for the instruction generator")
  parser.add_argument("--lsf_cmd", type=str, default="",
                      help="LSF command. Run in local sequentially if lsf \
                            command is not specified")
  parser.add_argument("-si", "--simulator", type=str, default="vcs",
                      help="Simulator used to run the generator, default VCS", dest="simulator")
  parser.set_defaults(verbose=False)
  parser.set_defaults(debug_mode=False)
  return parser

def main():
  """This is the main entry point."""
  parser = setup_parser()
  args = parser.parse_args()
  cwd = os.path.dirname(os.path.realpath(__file__))
  setup_logging(args.verbose)

  if args.verbose:
    args.opts += "-v"

  if not args.testlist:
    args.testlist = cwd + "/yaml/cov_testlist.yaml"

  # Create output directory
  if args.o is None:
    output_dir = "out_" + str(date.today())
  else:
    output_dir = args.o

  subprocess.run(["mkdir", "-p", output_dir])

  if args.debug_mode:
    run_cov_debug_test(output_dir, args.instr_cnt, args.testlist,
                       args.batch_size, args.opts, args.lsf_cmd, args.timeout, args.simulator)
  else:
    collect_cov(args.dir, output_dir, args.iss, args.testlist, args.batch_size,
                args.lsf_cmd, args.steps, args.opts, args.timeout, args.simulator)

if __name__ == "__main__":
  main()
