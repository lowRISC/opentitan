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

def collect_cov(log_dir, out, core, iss, testlist, batch_size, lsf_cmd, steps, \
                opts, timeout, simulator, simulator_yaml, custom_target, \
                isa, target, stop_on_first_error):
  """Collect functional coverage from the instruction trace

  Args:
    log_dir             : Trace log directory
    out                 : Output directory
    core                : RISC-V core to be used for analysis
    iss                 : Instruction set simulator
    testlist            : Testlist of the coverage test
    batch_size          : Number of trace CSV to process per test
    lsf_cmd             : LSF command used to run the instruction generator
    steps               : csv:log to CSV, cov:sample coverage
    opts                : Additional options to the instruction generator
    timeout             : Timeout limit in seconds
    simulator           : RTL simulator used to run
    simulator_yaml      : RTL simulator configuration file in YAML format
    custom_target       : Path for the custom target dir
    isa                 : RISC-V ISA variant
    target              : Predefined target
    stop_on_first_error : will end run on first error detected
  """
  cwd = os.path.dirname(os.path.realpath(__file__))
  log_list = []
  csv_list = []
  logging.info("Processing trace log under %s" % log_dir)
  if core:
    """
    If functional coverage is being collected from an RTL core implementation,
    the flow assumes that the core's trace logs have already been converted to
    CSV files by the post_compare step of the flow.
    """
    trace_log = ("%s/%s_trace_log" % (out, core))
    run_cmd("find %s -name \"*.csv\" | sort > %s" % (log_dir, trace_log))
  else:
    trace_log = ("%s/%s_trace_log" % (out, iss))
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
      # If a core target is defined, prioritize over ISS
      if core:
        logging.info("Process %0s log[%0d/%0d] : %s" % (core, i+1, len(log_list), log))
      else:
        logging.info("Process %0s log[%0d/%0d] : %s" % (iss, i+1, len(log_list), log))
        if iss == "spike":
          process_spike_sim_log(log, csv, 1)
        elif iss == "ovpsim":
          process_ovpsim_sim_log(log, csv, 1, stop_on_first_error)
        else:
          logging.error("Full trace for %s is not supported yet" % iss)
          sys.exit(1)
  if steps == "all" or re.match("cov", steps):
    build_cmd = ("python3 %s/run.py --simulator %s --simulator_yaml %s "
                 " --co -o %s --cov -tl %s %s " %
                 (cwd, simulator, simulator_yaml, out, testlist, opts))
    base_sim_cmd = ("python3 %s/run.py --simulator %s --simulator_yaml %s "
                    "--so -o %s --cov -tl %s %s "
                    "-tn riscv_instr_cov_test --steps gen --sim_opts \"<trace_csv_opts>\"" %
                    (cwd, simulator, simulator_yaml, out, testlist, opts))
    if target:
      build_cmd += (" --target %s" % target)
    if custom_target:
      build_cmd += (" --custom_target %s" % custom_target)
    if target:
      base_sim_cmd += (" --target %s" % target)
    if custom_target:
      base_sim_cmd += (" --custom_target %s" % custom_target)
    logging.info("Building the coverage collection framework")
    output = run_cmd(build_cmd)
    check_simulator_return(output, simulator, stop_on_first_error)
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
          check_simulator_return(output, simulator, stop_on_first_error)
        else:
          sim_cmd += (" --lsf_cmd \"%s\"" % lsf_cmd)
          sim_cmd_list.append(sim_cmd)
        trace_csv_opts = ""
    if lsf_cmd != "":
      run_parallel_cmd(sim_cmd_list, timeout)
    logging.info("Collecting functional coverage from %0d trace CSV...done" % len(csv_list))


def run_cov_debug_test(out, instr_cnt, testlist, batch_size, opts, lsf_cmd,\
                       timeout, simulator, simulator_yaml, custom_target, isa, target):
  """Collect functional coverage from the instruction trace

  Args:
    out              : Output directory
    instr_cnt        : Number of instruction to randomize
    test_list        : Testlist of the coverage test
    batch_size       : Number of trace CSV to process per test
    lsf_cmd          : LSF command used to run the instruction generator
    opts             : Additional options to the instruction generator
    timeout          : Timeout limit in seconds
    simulator        : RTL simulator used to run
    simulator_yaml   : RTL simulator configuration file in YAML format
    custom_target    : Path for the custom target dir
    isa              : RISC-V ISA variant
    target           : Predefined target
  """
  cwd = os.path.dirname(os.path.realpath(__file__))
  sim_cmd_list = []
  logging.info("Building the coverage collection framework")
  build_cmd = ("python3 %s/run.py --simulator %s --simulator_yaml %s "
               "--co -o %s --cov -tl %s %s" %
               (cwd, simulator, simulator_yaml, out, testlist, opts))
  if target:
    build_cmd += (" --target %s" % target)
  if custom_target:
    build_cmd += (" --custom_target %s" % custom_target)
  run_cmd(build_cmd)
  base_sim_cmd = ("python3 %s/run.py --simulator %s --simulator_yaml %s "
                  "--so -o %s --cov -tl %s --isa %s%s "
                  "-tn riscv_instr_cov_debug_test --steps gen "
                  "--sim_opts \"+num_of_iterations=<instr_cnt>\"" %
                  (cwd, simulator, simulator_yaml, out, testlist, isa, opts))
  if target:
    base_sim_cmd += (" --target %s" % target)
  if custom_target:
    base_sim_cmd += (" --custom_target %s" % custom_target)
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
                      help="Directory of trace log files")
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
  parser.add_argument("--core", type=str, default="",
                      help="Name of target core")
  parser.add_argument("--isa", type=str, default="",
                      help="RISC-V ISA variant")
  parser.add_argument("--iss", type=str, default="spike",
                      help="RISC-V instruction set simulator: spike,ovpsim,sail")
  parser.add_argument("-tl", "--testlist", type=str, default="",
                      help="Regression testlist", dest="testlist")
  parser.add_argument("--opts", type=str, default="",
                      help="Additional options for the instruction generator")
  parser.add_argument("--lsf_cmd", type=str, default="",
                      help="LSF command. Run in local sequentially if lsf \
                            command is not specified")
  parser.add_argument("--target", type=str, default="rv32imc",
                      help="Run the generator with pre-defined targets: \
                            rv32imc, rv32i, rv64imc, rv64gc")
  parser.add_argument("-si", "--simulator", type=str, default="vcs",
                      help="Simulator used to run the generator, \
                            default VCS", dest="simulator")
  parser.add_argument("--simulator_yaml", type=str, default="",
                      help="RTL simulator setting YAML")
  parser.add_argument("-ct", "--custom_target", type=str, default="",
                      help="Directory name of the custom target")
  parser.add_argument("-cs", "--core_setting_dir", type=str, default="",
                      help="Path for the riscv_core_setting.sv")
  parser.add_argument("--stop_on_first_error", dest="stop_on_first_error",
                      action="store_true", help="Stop on detecting first error")
  parser.set_defaults(verbose=False)
  parser.set_defaults(debug_mode=False)
  parser.set_defaults(stop_on_first_error=False)
  parser.add_argument("--noclean", action="store_true",
                      help="Do not clean the output of the previous runs")
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

  if not args.simulator_yaml:
    args.simulator_yaml = cwd + "/yaml/simulator.yaml"

  # Debug mode only works for RV64GC target
  if args.debug_mode:
    args.target = "rv64gc"

  # Disable ISS coverage if a core is passed in
  if args.core:
    args.iss = ""

  # Keep the core_setting_dir option to be backward compatible, suggest to use
  # --custom_target
  if args.core_setting_dir:
    if not args.custom_target:
      args.custom_target = args.core_setting_dir
  else:
    args.core_setting_dir = args.custom_target

  if not args.custom_target:
    args.core_setting_dir = cwd + "/target/"+ args.target

  args.testlist = cwd + "/yaml/cov_testlist.yaml" ## needed if need to force

  # Create output directory
  if args.o is None:
    output_dir = "cov_out_" + str(date.today())
  else:
    output_dir = args.o

  if args.noclean is False:
    os.system("rm -rf %s" % output_dir)

  subprocess.run(["mkdir", "-p", output_dir])

  if args.debug_mode:
    run_cov_debug_test(output_dir, args.instr_cnt, args.testlist,
                       args.batch_size, args.opts, args.lsf_cmd, args.timeout,
                       args.simulator, args.simulator_yaml, args.custom_target,
                       args.isa, args.target)
  else:
    collect_cov(args.dir, output_dir, args.core, args.iss, args.testlist,
                args.batch_size, args.lsf_cmd, args.steps, args.opts, args.timeout,
                args.simulator, args.simulator_yaml, args.custom_target,
                args.isa, args.target, args.stop_on_first_error)
    logging.info("Coverage results are saved to %s" % output_dir)

if __name__ == "__main__":
  main()
