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
import random
import re
import subprocess
import sys

sys.path.insert(0, "../../vendor/google_riscv-dv/scripts")
sys.path.insert(0, "./riscv_dv_extension")

from lib import *
from ibex_log_to_trace_csv import *
from spike_log_to_trace_csv import *
from ovpsim_log_to_trace_csv import *
from instr_trace_compare import *


def process_cmd(keyword, cmd, opts, enable):
  """ Process the compile and simulation command

  Args:
    keyword : Keyword to search
    cmd     : Command to be processed
    opts    : Options to replace the keyword
    enable  : Option enable/disable

  Returns:
    Processed command
  """
  if enable == "1":
    return re.sub(keyword, opts.rstrip(), cmd)
  else:
    return re.sub(keyword, "", cmd)


def get_simulator_cmd(simulator, simulator_yaml, en_cov, en_wave):
  """ Setup the compile and simulation command for the generator

  Args:
    simulator      : RTL simulator used to run instruction generator
    simulator_yaml : RTL simulator configuration file in YAML format
    en_cov         : Enable coverage dump
    en_wave        : Enable waveform

  Returns:
    compile_cmd    : RTL simulator command to compile the instruction generator
    sim_cmd        : RTL simulator command to run the instruction generator
  """
  logging.info("Processing simulator setup file : %s" % simulator_yaml)
  yaml_data = read_yaml(simulator_yaml)
  # Search for matched simulator
  for entry in yaml_data:
    if entry['tool'] == simulator:
      logging.info("Found matching simulator: %s" % entry['tool'])
      compile_cmd = entry['compile']['cmd']
      for i in range(len(compile_cmd)):
        if 'cov_opts' in entry['compile']:
          compile_cmd[i] = process_cmd("<cov_opts>", compile_cmd[i],
                                       entry['compile']['cov_opts'], en_cov)
        if 'wave_opts' in entry['compile']:
          compile_cmd[i] = process_cmd("<wave_opts>", compile_cmd[i],
                                       entry['compile']['wave_opts'], en_wave)
      sim_cmd = entry['sim']['cmd']
      if 'cov_opts' in entry['sim']:
        sim_cmd = process_cmd("<cov_opts>", sim_cmd, entry['sim']['cov_opts'], en_cov)
      if 'wave_opts' in entry['sim']:
        sim_cmd = process_cmd("<wave_opts>", sim_cmd, entry['sim']['wave_opts'], en_wave)
      if 'env_var' in entry:
        for env_var in entry['env_var'].split(','):
          for i in range(len(compile_cmd)):
            compile_cmd[i] = re.sub("<"+env_var+">", get_env_var(env_var), compile_cmd[i])
          sim_cmd = re.sub("<"+env_var+">", get_env_var(env_var), sim_cmd)
      return compile_cmd, sim_cmd
  logging.info("Cannot find RTL simulator %0s" % simulator)
  sys.exit(1)


def rtl_compile(compile_cmd, test_list, output_dir, lsf_cmd, opts):
  """Run the instruction generator

  Args:
    compile_cmd : Compile command
    test_list   : List of assembly programs to be compiled
    output_dir  : Output directory of the ELF files
    lsf_cmd     : LSF command to run compilation
    opts        : Compile options for the generator
  """
  # Compile the TB
  logging.info("Compiling TB")
  for cmd in compile_cmd:
    cmd = re.sub("<out>", output_dir, cmd)
    cmd = re.sub("<cmp_opts>", opts, cmd)
    logging.debug("Compile command: %s" % cmd)
    run_cmd(cmd)


def rtl_sim(sim_cmd, simulator, test_list, output_dir, bin_dir,
            lsf_cmd, seed, opts):
  """Run the instruction generator

  Args:
    sim_cmd    : Simulation command
    simulator  : Simulator being used
    test_list  : List of assembly programs
    output_dir : Simulation output directory
    bin_dir    : Directory of the ELF files
    lsf_cmd    : LSF command to run simulation
    seed       : Seed of RTL simulation
    opts       : Simulation options
  """
  check_return_code = True
  # Don't check return code for IUS sims, as a failure will short circuit
  # the entire simulation flow
  if simulator == "ius":
    check_return_code = False
    logging.debug("Disable return code checking for %s simulator" % simulator)
  # Run the RTL simulation
  sim_cmd = re.sub("<out>", output_dir, sim_cmd)
  sim_cmd = re.sub("<sim_opts>", opts, sim_cmd)
  sim_cmd = re.sub("<cwd>", cwd, sim_cmd)
  logging.info("Running RTL simulation...")
  cmd_list = []
  for test in test_list:
    for i in range(test['iterations']):
      rand_seed = get_seed(seed)
      test_sim_cmd = re.sub("<seed>", str(rand_seed), sim_cmd)
      if "sim_opts" in test:
        test_sim_cmd += ' '
        test_sim_cmd += test['sim_opts']
      sim_dir = output_dir + ("/%s.%d" %(test['test'], i))
      run_cmd(("mkdir -p %s" % sim_dir))
      os.chdir(sim_dir)
      binary = ("%s/%s_%d.bin" % (bin_dir, test['test'], i))
      cmd = lsf_cmd + " " + test_sim_cmd + \
            (" +UVM_TESTNAME=%s " % test['rtl_test']) + \
            (" +bin=%s " % binary) + \
            (" -l sim.log ")
      cmd = re.sub('\n', '', cmd)
      if lsf_cmd == "":
        logging.info("Running %s with %s" % (test['rtl_test'], binary))
        run_cmd(cmd, 300, check_return_code = check_return_code)
      else:
        cmd_list.append(cmd)
  if lsf_cmd != "":
    logging.info("Running %0d simulation jobs." % len(cmd_list))
    run_parallel_cmd(cmd_list, 600, check_return_code = check_return_code)


def compare(test_list, iss, output_dir, verbose):
  """Compare RTL & ISS simulation reult

  Args:
    test_list   : List of assembly programs to be compiled
    iss         : List of instruction set simulators
    output_dir  : Output directory of the ELF files
    verbose     : Verbose logging
  """
  report = ("%s/regr.log" % output_dir).rstrip()
  for test in test_list:
    compare_opts = test.get('compare_opts', {})
    in_order_mode = compare_opts.get('in_order_mode', 1)
    coalescing_limit = compare_opts.get('coalescing_limit', 0)
    verbose = compare_opts.get('verbose', 0)
    mismatch = compare_opts.get('mismatch_print_limit', 5)
    compare_final = compare_opts.get('compare_final_value_only', 0)
    for i in range(0, test['iterations']):
      elf = ("%s/asm_tests/%s.%d.o" % (output_dir, test['test'], i))
      logging.info("Comparing %s/DUT sim result : %s" % (iss, elf))
      run_cmd(("echo 'Test binary: %s' >> %s" % (elf, report)))
      uvm_log = ("%s/rtl_sim/%s.%d/sim.log" % (output_dir, test['test'], i))
      rtl_log = ("%s/rtl_sim/%s.%d/trace_core_00000000.log" % (output_dir, test['test'], i))
      rtl_csv = ("%s/rtl_sim/%s.%d/trace_core_00000000.csv" % (output_dir, test['test'], i))
      test_name = "%s.%d" % (test['test'], i)
      process_ibex_sim_log(rtl_log, rtl_csv, 1)
      if 'no_post_compare' in test and test['no_post_compare'] == 1:
        check_ibex_uvm_log(uvm_log, "ibex", test_name, report)
      else:
        iss_log = ("%s/instr_gen/%s_sim/%s.%d.log" % (output_dir, iss, test['test'], i))
        iss_csv = ("%s/instr_gen/%s_sim/%s.%d.csv" % (output_dir, iss, test['test'], i))
        if iss == "spike":
          process_spike_sim_log(iss_log, iss_csv)
        elif iss == "ovpsim":
          process_ovpsim_sim_log(iss_log, iss_csv)
        else:
          logging.info("Unsupported ISS" % iss)
          sys.exit(1)
        uvm_result = check_ibex_uvm_log(uvm_log, "ibex", test_name, report, False)
        if not uvm_result:
          check_ibex_uvm_log(uvm_log, "ibex", test_name, report)
        else:
          if 'compare_opts' in test:
            compare_trace_csv(rtl_csv, iss_csv, "ibex", iss, report,
                              in_order_mode, coalescing_limit, verbose,
                              mismatch, compare_final)
          else:
            compare_trace_csv(rtl_csv, iss_csv, "ibex", iss, report)
  passed_cnt = run_cmd("grep PASSED %s | wc -l" % report).strip()
  failed_cnt = run_cmd("grep FAILED %s | wc -l" % report).strip()
  summary = ("%s PASSED, %s FAILED" % (passed_cnt, failed_cnt))
  logging.info(summary)
  run_cmd(("echo %s >> %s" % (summary, report)))
  logging.info("RTL & ISS regression report is saved to %s" % report)


# Parse input arguments
parser = argparse.ArgumentParser()

parser.add_argument("--o", type=str, default="./out",
                    help="Output directory name")
parser.add_argument("--riscv_dv_root", type=str, default="",
                    help="Root directory of RISCV-DV")
parser.add_argument("--testlist", type=str, default="riscv_dv_extension/testlist.yaml",
                    help="Regression testlist")
parser.add_argument("--test", type=str, default="all",
                    help="Test name, 'all' means all tests in the list")
parser.add_argument("--seed", type=int, default=-1,
                    help="Randomization seed, default -1 means random seed")
parser.add_argument("--iterations", type=int, default=0,
                    help="Override the iteration count in the test list")
parser.add_argument("--simulator", type=str, default="vcs",
                    help="Simulator used to run the generator, default VCS")
parser.add_argument("--simulator_yaml", type=str, default="yaml/rtl_simulation.yaml",
                    help="RTL simulator setting YAML")
parser.add_argument("--iss", type=str, default="spike",
                    help="Instruction set simulator")
parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                    help="Verbose logging")
parser.add_argument("--cmp_opts", type=str, default="",
                    help="Compile options for the generator")
parser.add_argument("--sim_opts", type=str, default="",
                    help="Simulation options for the generator")
parser.add_argument("--en_cov", type=str, default=0,
                    help="Enable coverage dump")
parser.add_argument("--en_wave", type=str, default=0,
                    help="Enable waveform dump")
parser.add_argument("--steps", type=str, default="all",
                    help="Run steps: compile,sim,compare")
parser.add_argument("--lsf_cmd", type=str, default="",
                    help="LSF command. Run in local sequentially if lsf \
                          command is not specified")

args = parser.parse_args()
setup_logging(args.verbose)
parser.set_defaults(verbose=False)
cwd = os.path.dirname(os.path.realpath(__file__))

# Create the output directory
output_dir = ("%s/rtl_sim" % args.o)
bin_dir = ("%s/instr_gen/asm_tests" % args.o)
subprocess.run(["mkdir", "-p", output_dir])

# Process regression test list
matched_list = []
process_regression_list(args.testlist, args.test, args.iterations,
                        matched_list, args.riscv_dv_root)
if len(matched_list) == 0:
  sys.exit("Cannot find %s in %s" % (args.test, args.testlist))

compile_cmd = []
sim_cmd = ""
compile_cmd, sim_cmd = get_simulator_cmd(args.simulator, args.simulator_yaml,
                                         args.en_cov, args.en_wave)
# Compile TB
if args.steps == "all" or re.match("compile", args.steps):
  rtl_compile(compile_cmd, matched_list, output_dir, args.lsf_cmd, args.cmp_opts)

# Run RTL simulation
if args.steps == "all" or re.match("sim", args.steps):
  rtl_sim(sim_cmd, args.simulator, matched_list, output_dir, bin_dir,
          args.lsf_cmd, args.seed, args.sim_opts)

# Compare RTL & ISS simulation result.;
if args.steps == "all" or re.match("compare", args.steps):
  compare(matched_list, args.iss, args.o, args.verbose)
