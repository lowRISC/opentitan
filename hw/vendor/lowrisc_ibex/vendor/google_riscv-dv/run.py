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
from scripts.whisper_log_trace_csv import *
from scripts.sail_log_to_trace_csv import *
from scripts.instr_trace_compare import *

LOGGER = logging.getLogger()

def get_generator_cmd(simulator, simulator_yaml, cov):
  """ Setup the compile and simulation command for the generator

  Args:
    simulator      : RTL simulator used to run instruction generator
    simulator_yaml : RTL simulator configuration file in YAML format
    cov            : Enable functional coverage

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
      compile_spec = entry['compile']
      compile_cmd = compile_spec['cmd']
      for i in range(len(compile_cmd)):
        if ('cov_opts' in compile_spec) and cov:
          compile_cmd[i] = re.sub('<cov_opts>', compile_spec['cov_opts'].rstrip(), compile_cmd[i])
        else:
          compile_cmd[i] = re.sub('<cov_opts>', '', compile_cmd[i])
      sim_cmd = entry['sim']['cmd']
      if ('cov_opts' in entry['sim']) and cov:
        sim_cmd = re.sub('<cov_opts>', entry['sim']['cov_opts'].rstrip(), sim_cmd)
      else:
        sim_cmd = re.sub('<cov_opts>', '', sim_cmd)
      if 'env_var' in entry:
        for env_var in entry['env_var'].split(','):
          for i in range(len(compile_cmd)):
            compile_cmd[i] = re.sub("<"+env_var+">", get_env_var(env_var), compile_cmd[i])
          sim_cmd = re.sub("<"+env_var+">", get_env_var(env_var), sim_cmd)
      return compile_cmd, sim_cmd
  logging.error("Cannot find RTL simulator %0s" % simulator)
  sys.exit(1)


def parse_iss_yaml(iss, iss_yaml, isa, setting_dir):
  """Parse ISS YAML to get the simulation command

  Args:
    iss         : target ISS used to look up in ISS YAML
    iss_yaml    : ISS configuration file in YAML format
    isa         : ISA variant passed to the ISS
    setting_dir : Generator setting directory

  Returns:
    cmd         : ISS run command
  """
  logging.info("Processing ISS setup file : %s" % iss_yaml)
  yaml_data = read_yaml(iss_yaml)
  cwd = os.path.dirname(os.path.realpath(__file__))
  # Search for matched ISS
  for entry in yaml_data:
    if entry['iss'] == iss:
      logging.info("Found matching ISS: %s" % entry['iss'])
      cmd = entry['cmd'].rstrip()
      cmd = re.sub("\<path_var\>", get_env_var(entry['path_var']), cmd)
      if iss == "ovpsim":
        cmd = re.sub("\<cfg_path\>", setting_dir, cmd)
      elif iss == "whisper":
        m = re.search(r"rv(?P<xlen>[0-9]+?)(?P<variant>[a-z]+?)$", isa)
        if m:
          # TODO: Support u/s mode
          cmd = re.sub("\<xlen\>", m.group('xlen'), cmd)
          variant = re.sub('g', 'imafd',  m.group('variant'))
          cmd = re.sub("\<variant\>", variant, cmd)
        else:
          logging.error("Illegal ISA %0s" % isa)
        cmd = re.sub("\<xlen\>", setting_dir, cmd)
      else:
        cmd = re.sub("\<variant\>", isa, cmd)
      return cmd
  logging.error("Cannot find ISS %0s" % iss)
  sys.exit(1)


def get_iss_cmd(base_cmd, elf, log):
  """Get the ISS simulation command

  Args:
    base_cmd : Original command template
    elf      : ELF file to run ISS simualtion
    log      : ISS simulation log name

  Returns:
    cmd      : Command for ISS simulation
  """
  cmd = re.sub("\<elf\>", elf, base_cmd)
  cmd += (" &> %s" % log)
  return cmd


def gen(test_list, csr_file, end_signature_addr, isa, simulator,
        simulator_yaml, output_dir, sim_only, compile_only, lsf_cmd, seed,
        cwd, cmp_opts, sim_opts, timeout_s, core_setting_dir, ext_dir, cov,
        log_suffix, batch_size, seed_yaml, stop_on_first_error, verbose=False):
  """Run the instruction generator

  Args:
    test_list             : List of assembly programs to be compiled
    csr_file              : YAML file containing description of all CSRs
    end_signature_addr    : Address that tests will write pass/fail signature to at end of test
    isa                   : Processor supported ISA subset
    simulator             : RTL simulator used to run instruction generator
    simulator_yaml        : RTL simulator configuration file in YAML format
    output_dir            : Output directory of the ELF files
    sim_only              : Simulation only
    compile_only          : Compile the generator only
    lsf_cmd               : LSF command used to run the instruction generator
    cwd                   : Filesystem path to RISCV-DV repo
    seed                  : Seed to the instruction generator
    cmp_opts              : Compile options for the generator
    sim_opts              : Simulation options for the generator
    timeout_s             : Timeout limit in seconds
    core_setting_dir      : Path for riscv_core_setting.sv
    ext_dir               : User extension directory
    cov                   : Enable functional coverage
    log_suffix            : Simulation log file name suffix
    batch_size            : Number of tests to generate per run
    seed_yaml             : Seed specification from a prior regression
    stop_on_first_error   : will end run on first error detected
  """
  # Mutually exclusive options between compile_only and sim_only
  if compile_only and sim_only:
    logging.error("argument -co is not allowed with argument -so")
  # Setup the compile and simulation command for the generator
  compile_cmd = []
  sim_cmd = ""
  compile_cmd, sim_cmd = get_generator_cmd(simulator, simulator_yaml, cov);
  if ((compile_only == 0) and (len(test_list) == 0)):
    return
  # Compile the instruction generator
  if not sim_only:
    if (not((len(test_list) == 1) and (test_list[0]['test'] == 'riscv_csr_test'))):
      logging.info("Building RISC-V instruction generator")
      for cmd in compile_cmd:
        cmd = re.sub("<out>", os.path.abspath(output_dir), cmd)
        cmd = re.sub("<setting>", core_setting_dir, cmd)
        if ext_dir == "":
          cmd = re.sub("<user_extension>", "<cwd>/user_extension", cmd)
        else:
          cmd = re.sub("<user_extension>", ext_dir, cmd)
        cmd = re.sub("<cwd>", cwd, cmd)
        cmd = re.sub("<cmp_opts>", cmp_opts, cmd)

        logging.debug("Compile command: %s" % cmd)
        output = run_cmd(cmd)
  # Run the instruction generator
  if not compile_only:
    cmd_list = []
    sim_cmd = re.sub("<out>", os.path.abspath(output_dir), sim_cmd)
    sim_cmd = re.sub("<cwd>", cwd, sim_cmd)
    sim_cmd = re.sub("<sim_opts>", sim_opts, sim_cmd)
    if seed_yaml:
      rerun_seed = read_yaml(seed_yaml)
    else:
      rerun_seed = {}
    logging.info("Running RISC-V instruction generator")
    sim_seed = {}
    for test in test_list:
      iterations = test['iterations']
      logging.info("Generating %d %s" % (iterations, test['test']))
      if iterations > 0:
        """
        If we are running a CSR test, need to call a separate python script
        to generate directed CSR test code, located at scripts/gen_csr_test.py.
        """
        if test['test'] == 'riscv_csr_test':
          cmd = "python3 " + cwd + "/scripts/gen_csr_test.py" + \
                (" --csr_file %s" % csr_file) + \
                (" --xlen %s" % re.search(r"(?P<xlen>[0-9]+)", isa).group("xlen")) + \
                (" --iterations %i" % iterations) + \
                (" --out %s/asm_tests" % output_dir) + \
                (" --end_signature_addr %s" % end_signature_addr)
          if lsf_cmd:
            cmd_list.append(cmd)
          else:
            output = run_cmd(cmd, timeout_s)
        else:
          if batch_size > 0:
            batch_cnt = int((iterations + batch_size - 1)  / batch_size);
          else:
            batch_cnt = 1
          logging.info("Running %s with %0d batches" % (test['test'], batch_cnt))
          for i in range(0, batch_cnt):
            test_id = '%0s_%0d' % (test['test'], i)
            if test_id in rerun_seed:
              rand_seed = rerun_seed[test_id]
            else:
              rand_seed = get_seed(seed)
            if i < batch_cnt - 1:
              test_cnt = batch_size
            else:
              test_cnt = iterations - i * batch_size;
            cmd = lsf_cmd + " " + sim_cmd.rstrip() + \
                  (" +UVM_TESTNAME=%s " % test['gen_test']) + \
                  (" +num_of_tests=%i " % test_cnt) + \
                  (" +start_idx=%d " % (i*batch_size)) + \
                  (" +asm_file_name=%s/asm_tests/%s " % (output_dir, test['test'])) + \
                  (" -l %s/sim_%s_%d%s.log " % (output_dir, test['test'], i, log_suffix))
            if verbose:
              cmd += "+UVM_VERBOSITY=UVM_HIGH "
            cmd = re.sub("<seed>", str(rand_seed), cmd)
            sim_seed[test_id] = str(rand_seed)
            if "gen_opts" in test:
              cmd += test['gen_opts']
            if not re.search("c", isa):
              cmd += "+disable_compressed_instr=1 ";
            if lsf_cmd:
              cmd_list.append(cmd)
            else:
              logging.info("Running %s, batch %0d/%0d, test_cnt:%0d" %
                           (test['test'], i+1, batch_cnt, test_cnt))
              output = run_cmd(cmd, timeout_s)
    if sim_seed:
      with open(('%s/seed.yaml' % os.path.abspath(output_dir)) , 'w') as outfile:
        yaml.dump(sim_seed, outfile, default_flow_style=False)
    if lsf_cmd:
      run_parallel_cmd(cmd_list, timeout_s)


def gcc_compile(test_list, output_dir, isa, mabi, opts):
  """Use riscv gcc toolchain to compile the assembly program

  Args:
    test_list  : List of assembly programs to be compiled
    output_dir : Output directory of the ELF files
    isa        : ISA variant passed to GCC
    mabi       : MABI variant passed to GCC
  """
  cwd = os.path.dirname(os.path.realpath(__file__))
  for test in test_list:
    for i in range(0, test['iterations']):
      if 'no_gcc' in test and test['no_gcc'] == 1:
        continue
      prefix = ("%s/asm_tests/%s_%d" % (output_dir, test['test'], i))
      asm = prefix + ".S"
      elf = prefix + ".o"
      binary = prefix + ".bin"
      test_isa = isa
      # gcc comilation
      cmd = ("%s -static -mcmodel=medany \
             -fvisibility=hidden -nostdlib \
             -nostartfiles %s \
             -I%s/user_extension \
             -T%s/scripts/link.ld %s -o %s " % \
             (get_env_var("RISCV_GCC"), asm, cwd, cwd, opts, elf))
      if 'gcc_opts' in test:
        cmd += test['gcc_opts']
      if 'gen_opts' in test:
        # Disable compressed instruction
        if re.search('disable_compressed_instr', test['gen_opts']):
          test_isa = re.sub("c",  "", test_isa)
      # If march/mabi is not defined in the test gcc_opts, use the default
      # setting from the command line.
      if not re.search('march', cmd):
        cmd += (" -march=%s" % test_isa)
      if not re.search('mabi', cmd):
        cmd += (" -mabi=%s" % mabi)
      logging.info("Compiling %s" % asm)
      logging.debug(cmd)
      output = subprocess.check_output(cmd.split())
      logging.debug(output)
      # Convert the ELF to plain binary, used in RTL sim
      logging.info("Converting to %s" % binary)
      cmd = ("%s -O binary %s %s" % (get_env_var("RISCV_OBJCOPY"), elf, binary))
      output = subprocess.check_output(cmd.split())
      logging.debug(output)


def run_assembly(asm_test, iss_yaml, isa, mabi, iss):
  """Run a directed assembly test with spike

  Args:
    asm_tset   : Assembly test file
    iss_yaml   : ISS configuration file in YAML format
    isa        : ISA variant passed to the ISS
    mabi       : MABI variant passed to GCC
    iss        : Instruction set simulators
  """
  cwd = os.path.dirname(os.path.realpath(__file__))
  asm = asm_test
  elf = asm_test + ".o"
  binary = asm_test + ".bin"
  log = asm_test + ".log"
  logging.info("Compiling assembly test : %s" % asm)
  # gcc comilation
  cmd = ("%s -static -mcmodel=medany \
         -fvisibility=hidden -nostdlib \
         -nostartfiles %s \
         -I%s/user_extension \
         -T%s/scripts/link.ld -o %s " % \
         (get_env_var("RISCV_GCC"), asm, cwd, cwd, elf))
  cmd += (" -march=%s" % isa)
  cmd += (" -mabi=%s" % mabi)
  logging.info("Compiling %s" % asm)
  output = subprocess.check_output(cmd.split())
  # Convert the ELF to plain binary, used in RTL sim
  logging.info("Converting to %s" % binary)
  cmd = ("%s -O binary %s %s" % (get_env_var("RISCV_OBJCOPY"), elf, binary))
  output = subprocess.check_output(cmd.split())
  logging.debug(output)
  base_cmd = parse_iss_yaml(iss, iss_yaml, isa)
  logging.info("[%0s] Running ISS simulation: %s" % (iss, elf))
  cmd = get_iss_cmd(base_cmd, elf, log)
  run_cmd(cmd, 20)
  logging.info("[%0s] Running ISS simulation: %s ...done" % (iss, elf))


def iss_sim(test_list, output_dir, iss_list, iss_yaml, isa, setting_dir, timeout_s):
  """Run ISS simulation with the generated test program

  Args:
    test_list   : List of assembly programs to be compiled
    output_dir  : Output directory of the ELF files
    iss_list    : List of instruction set simulators
    iss_yaml    : ISS configuration file in YAML format
    isa         : ISA variant passed to the ISS
    setting_dir : Generator setting directory
    timeout_s   : Timeout limit in seconds
  """
  for iss in iss_list.split(","):
    log_dir = ("%s/%s_sim" % (output_dir, iss))
    base_cmd = parse_iss_yaml(iss, iss_yaml, isa, setting_dir)
    logging.info("%s sim log dir: %s" % (iss, log_dir))
    subprocess.run(["mkdir", "-p", log_dir])
    for test in test_list:
      if 'no_iss' in test and test['no_iss'] == 1:
        continue
      else:
        for i in range(0, test['iterations']):
          prefix = ("%s/asm_tests/%s_%d" % (output_dir, test['test'], i))
          elf = prefix + ".o"
          log = ("%s/%s.%d.log" % (log_dir, test['test'], i))
          cmd = get_iss_cmd(base_cmd, elf, log)
          logging.info("Running %s sim: %s" % (iss, elf))
          run_cmd(cmd, timeout_s)
          logging.debug(cmd)


def iss_cmp(test_list, iss, output_dir, isa, stop_on_first_error):
  """Compare ISS simulation reult

  Args:
    test_list      : List of assembly programs to be compiled
    iss            : List of instruction set simulators
    output_dir     : Output directory of the ELF files
    isa            : ISA
    stop_on_first_error : will end run on first error detected
  """
  iss_list = iss.split(",")
  if len(iss_list) != 2:
    return
  report = ("%s/iss_regr.log" % output_dir).rstrip()
  run_cmd("rm -rf %s" % report)
  for test in test_list:
    for i in range(0, test['iterations']):
      elf = ("%s/asm_tests/%s_%d.o" % (output_dir, test['test'], i))
      logging.info("Comparing ISS sim result %s/%s : %s" %
                  (iss_list[0], iss_list[1], elf))
      csv_list = []
      run_cmd(("echo 'Test binary: %s' >> %s" % (elf, report)))
      for iss in iss_list:
        log = ("%s/%s_sim/%s.%d.log" % (output_dir, iss, test['test'], i))
        csv = ("%s/%s_sim/%s.%d.csv" % (output_dir, iss, test['test'], i))
        csv_list.append(csv)
        if iss == "spike":
          process_spike_sim_log(log, csv)
        elif iss == "ovpsim":
          process_ovpsim_sim_log(log, csv, 1, stop_on_first_error)
        elif iss == "sail":
          process_sail_sim_log(log, csv)
        elif iss == "whisper":
          process_whisper_sim_log(log, csv)
        else:
          logging.error("Unsupported ISS" % iss)
          sys.exit(1)
      compare_trace_csv(csv_list[0], csv_list[1], iss_list[0], iss_list[1], report)
  passed_cnt = run_cmd("grep PASSED %s | wc -l" % report).strip()
  failed_cnt = run_cmd("grep FAILED %s | wc -l" % report).strip()
  summary = ("%s PASSED, %s FAILED" % (passed_cnt, failed_cnt))
  logging.info(summary)
  run_cmd(("echo %s >> %s" % (summary, report)))
  logging.info("ISS regression report is saved to %s" % report)


def setup_parser():
  """Create a command line parser.

  Returns: The created parser.
  """
  # Parse input arguments
  parser = argparse.ArgumentParser()

  parser.add_argument("--target", type=str, default="rv32imc",
                      help="Run the generator with pre-defined targets: \
                            rv32imc, rv32i, rv64imc, rv64gc")
  parser.add_argument("-o", "--output", type=str,
                      help="Output directory name", dest="o")
  parser.add_argument("-tl", "--testlist", type=str, default="",
                      help="Regression testlist", dest="testlist")
  parser.add_argument("-tn", "--test", type=str, default="all",
                      help="Test name, 'all' means all tests in the list", dest="test")
  parser.add_argument("--seed", type=int, default=-1,
                      help="Randomization seed, default -1 means random seed")
  parser.add_argument("-i", "--iterations", type=int, default=0,
                      help="Override the iteration count in the test list", dest="iterations")
  parser.add_argument("-si", "--simulator", type=str, default="vcs",
                      help="Simulator used to run the generator, default VCS", dest="simulator")
  parser.add_argument("--iss", type=str, default="spike",
                      help="RISC-V instruction set simulator: spike,ovpsim,sail")
  parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                      help="Verbose logging")
  parser.add_argument("--co", dest="co", action="store_true",
                      help="Compile the generator only")
  parser.add_argument("--cov", dest="cov", action="store_true",
                      help="Enable functional coverage")
  parser.add_argument("--so", dest="so", action="store_true",
                      help="Simulate the generator only")
  parser.add_argument("--cmp_opts", type=str, default="",
                      help="Compile options for the generator")
  parser.add_argument("--sim_opts", type=str, default="",
                      help="Simulation options for the generator")
  parser.add_argument("--gcc_opts", type=str, default="",
                      help="GCC compile options")
  parser.add_argument("-s", "--steps", type=str, default="all",
                      help="Run steps: gen,gcc_compile,iss_sim,iss_cmp", dest="steps")
  parser.add_argument("--lsf_cmd", type=str, default="",
                      help="LSF command. Run in local sequentially if lsf \
                            command is not specified")
  parser.add_argument("--isa", type=str, default="",
                      help="RISC-V ISA subset")
  parser.add_argument("-m", "--mabi", type=str, default="",
                      help="mabi used for compilation", dest="mabi")
  parser.add_argument("--gen_timeout", type=int, default=360,
                      help="Generator timeout limit in seconds")
  parser.add_argument("--end_signature_addr", type=str, default="0",
                      help="Address that privileged CSR test writes to at EOT")
  parser.add_argument("--iss_timeout", type=int, default=10,
                      help="ISS sim timeout limit in seconds")
  parser.add_argument("--iss_yaml", type=str, default="",
                      help="ISS setting YAML")
  parser.add_argument("--simulator_yaml", type=str, default="",
                      help="RTL simulator setting YAML")
  parser.add_argument("--csr_yaml", type=str, default="",
                      help="CSR description file")
  parser.add_argument("--seed_yaml", type=str, default="",
                      help="Rerun the generator with the seed specification \
                            from a prior regression")
  parser.add_argument("-ct", "--custom_target", type=str, default="",
                      help="Directory name of the custom target")
  parser.add_argument("-cs", "--core_setting_dir", type=str, default="",
                      help="Path for the riscv_core_setting.sv")
  parser.add_argument("-ext", "--user_extension_dir", type=str, default="",
                      help="Path for the user extension directory")
  parser.add_argument("--asm_test", type=str, default="",
                      help="Directed assembly test")
  parser.add_argument("--log_suffix", type=str, default="",
                      help="Simulation log name suffix")
  parser.add_argument("-bz", "--batch_size", type=int, default=0,
                      help="Number of tests to generate per run. You can split a big"
                           " job to small batches with this option")
  parser.add_argument("--stop_on_first_error", dest="stop_on_first_error", action="store_true",
                      help="Stop on detecting first error")
  parser.set_defaults(co=False)
  parser.set_defaults(so=False)
  parser.set_defaults(verbose=False)
  parser.set_defaults(cov=False)
  parser.set_defaults(stop_on_first_error=False)
  return parser


def main():
  """This is the main entry point."""
  parser = setup_parser()
  args = parser.parse_args()
  cwd = os.path.dirname(os.path.realpath(__file__))
  os.environ["RISCV_DV_ROOT"] = cwd
  setup_logging(args.verbose)

  if not args.csr_yaml:
    args.csr_yaml = cwd + "/yaml/csr_template.yaml"

  if not args.iss_yaml:
    args.iss_yaml = cwd + "/yaml/iss.yaml"

  if not args.simulator_yaml:
    args.simulator_yaml = cwd + "/yaml/simulator.yaml"

  # Keep the core_setting_dir option to be backward compatible, suggest to use
  # --custom_target
  if args.core_setting_dir:
    if not args.custom_target:
      args.custom_target = args.core_setting_dir
  else:
    args.core_setting_dir = args.custom_target

  if not args.custom_target:
    if not args.testlist:
      args.testlist = cwd + "/target/"+ args.target +"/testlist.yaml"
    args.core_setting_dir = cwd + "/target/"+ args.target
    if args.target == "rv32imc":
      args.mabi = "ilp32"
      args.isa  = "rv32imc"
    elif args.target == "rv32i":
      args.mabi = "ilp32"
      args.isa  = "rv32i"
    elif args.target == "rv64imc":
      args.mabi = "lp64"
      args.isa  = "rv64imc"
    elif args.target == "rv64gc":
      args.mabi = "lp64"
      args.isa  = "rv64gc"
    elif args.target == "ml":
      args.mabi = "lp64"
      args.isa  = "rv64imc"
    else:
      print ("Unsupported pre-defined target: %0s" % args.target)
  else:
    if re.match(".*gcc_compile.*", args.steps) or re.match(".*iss_sim.*", args.steps):
      if (not args.mabi) or (not args.isa):
        sys.exit("mabi and isa must be specified for custom target %0s" % args.custom_target)
    if not args.testlist:
      args.testlist = args.custom_target + "/testlist.yaml"

  if args.asm_test != "":
    run_assembly(args.asm_test, args.iss_yaml, args.isa, args.mabi, args.iss)
    return

  # Create output directory
  if args.o is None:
    output_dir = "out_" + str(date.today())
  else:
    output_dir = args.o

  subprocess.run(["mkdir", "-p", output_dir])
  subprocess.run(["mkdir", "-p", ("%s/asm_tests" % output_dir)])

  # Process regression test list
  matched_list = []

  if not args.co:
    process_regression_list(args.testlist, args.test, args.iterations, matched_list, cwd)
    if len(matched_list) == 0:
      sys.exit("Cannot find %s in %s" % (args.test, args.testlist))

  # Run instruction generator
  if args.steps == "all" or re.match(".*gen.*", args.steps):
    gen(matched_list, args.csr_yaml, args.end_signature_addr, args.isa,
        args.simulator, args.simulator_yaml, output_dir, args.so,
        args.co, args.lsf_cmd, args.seed, cwd, args.cmp_opts,
        args.sim_opts, args.gen_timeout, args.core_setting_dir,
        args.user_extension_dir, args.cov, args.log_suffix, args.batch_size,
        args.seed_yaml, args.stop_on_first_error, args.verbose)

  if not args.co:
    # Compile the assembly program to ELF, convert to plain binary
    if args.steps == "all" or re.match(".*gcc_compile.*", args.steps):
      gcc_compile(matched_list, output_dir, args.isa, args.mabi, args.gcc_opts)

    # Run ISS simulation
    if args.steps == "all" or re.match(".*iss_sim.*", args.steps):
      iss_sim(matched_list, output_dir, args.iss, args.iss_yaml,
              args.isa, args.core_setting_dir, args.iss_timeout)

    # Compare ISS simulation result
    if args.steps == "all" or re.match(".*iss_cmp.*", args.steps):
      iss_cmp(matched_list, args.iss, output_dir, args.isa, args.stop_on_first_error)

if __name__ == "__main__":
  main()
