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
import re
import sys
import logging

from scripts.lib import *
from scripts.spike_log_to_trace_csv import *
from scripts.ovpsim_log_to_trace_csv import *
from scripts.whisper_log_trace_csv import *
from scripts.sail_log_to_trace_csv import *
from scripts.instr_trace_compare import *

from types import SimpleNamespace

LOGGER = logging.getLogger()

def get_generator_cmd(simulator, simulator_yaml, cov, exp):
  """ Setup the compile and simulation command for the generator

  Args:
    simulator      : RTL simulator used to run instruction generator
    simulator_yaml : RTL simulator configuration file in YAML format
    cov            : Enable functional coverage
    exp            : Use experimental version

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
        if exp:
          compile_cmd[i] += " +define+EXPERIMENTAL "
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
  sys.exit(RET_FAIL)


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
  # Search for matched ISS
  for entry in yaml_data:
    if entry['iss'] == iss:
      logging.info("Found matching ISS: %s" % entry['iss'])
      cmd = entry['cmd'].rstrip()
      cmd = re.sub("\<path_var\>", get_env_var(entry['path_var']), cmd)
      m = re.search(r"rv(?P<xlen>[0-9]+?)(?P<variant>[a-z]+?)$", isa)
      if m:
        cmd = re.sub("\<xlen\>", m.group('xlen'), cmd)
      else:
        logging.error("Illegal ISA %0s" % isa)
      if iss == "ovpsim":
        cmd = re.sub("\<cfg_path\>", setting_dir, cmd)
      elif iss == "whisper":
        if m:
          # TODO: Support u/s mode
          variant = re.sub('g', 'imafd',  m.group('variant'))
          cmd = re.sub("\<variant\>", variant, cmd)
      else:
        cmd = re.sub("\<variant\>", isa, cmd)
      return cmd
  logging.error("Cannot find ISS %0s" % iss)
  sys.exit(RET_FAIL)


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

def do_compile(compile_cmd, test_list, core_setting_dir, cwd, ext_dir, cmp_opts, output_dir):
  """Compile the instruction generator

  Args:
    compile_cmd         : Compile command for the generator
    test_list           : List of assembly programs to be compiled
    core_setting_dir    : Path for riscv_core_setting.sv
    cwd                 : Filesystem path to RISCV-DV repo
    ext_dir             : User extension directory
    cmd_opts            : Compile options for the generator
    output_dir          : Output directory of the ELF files
  """
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
      run_cmd(cmd)

def run_csr_test(cmd_list, cwd, csr_file, isa, iterations, lsf_cmd,
                 end_signature_addr, timeout_s, output_dir):
  """Run CSR test
     It calls a separate python script to generate directed CSR test code,
     located at scripts/gen_csr_test.py.
  """
  cmd = "python3 " + cwd + "/scripts/gen_csr_test.py" + \
        (" --csr_file %s" % csr_file) + \
        (" --xlen %s" % re.search(r"(?P<xlen>[0-9]+)", isa).group("xlen")) + \
        (" --iterations %i" % iterations) + \
        (" --out %s/asm_tests" % output_dir) + \
        (" --end_signature_addr %s" % end_signature_addr)
  if lsf_cmd:
    cmd_list.append(cmd)
  else:
    run_cmd(cmd, timeout_s)

def do_simulate(sim_cmd, test_list, cwd, sim_opts, seed_yaml, seed, csr_file,
                isa, end_signature_addr, lsf_cmd, timeout_s, log_suffix,
                batch_size, output_dir, verbose, check_return_code):
  """Run  the instruction generator

  Args:
    sim_cmd               : Simulate command for the generator
    test_list             : List of assembly programs to be compiled
    cwd                   : Filesystem path to RISCV-DV repo
    sim_opts              : Simulation options for the generator
    seed_yaml             : Seed specification from a prior regression
    seed                  : Seed to the instruction generator
    csr_file              : YAML file containing description of all CSRs
    isa                   : Processor supported ISA subset
    end_signature_addr    : Address that tests will write pass/fail signature to at end of test
    lsf_cmd               : LSF command used to run the instruction generator
    timeout_s             : Timeout limit in seconds
    log_suffix            : Simulation log file name suffix
    batch_size            : Number of tests to generate per run
    output_dir            : Output directory of the ELF files
    check_return_code     : Check return code of the command
  """
  cmd_list = []
  sim_cmd = re.sub("<out>", os.path.abspath(output_dir), sim_cmd)
  sim_cmd = re.sub("<cwd>", cwd, sim_cmd)
  sim_cmd = re.sub("<sim_opts>", sim_opts, sim_cmd)
  rerun_seed = {}
  if seed_yaml:
    rerun_seed = read_yaml(seed_yaml)
  logging.info("Running RISC-V instruction generator")
  sim_seed = {}
  for test in test_list:
    iterations = test['iterations']
    logging.info("Generating %d %s" % (iterations, test['test']))
    if iterations > 0:
      # Running a CSR test
      if test['test'] == 'riscv_csr_test':
        run_csr_test(cmd_list, cwd, csr_file, isa, iterations, lsf_cmd,
                     end_signature_addr, timeout_s, output_dir)
      else:
        batch_cnt = 1
        if batch_size > 0:
          batch_cnt = int((iterations + batch_size - 1)  / batch_size);
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
            run_cmd(cmd, timeout_s, check_return_code = check_return_code)
  if sim_seed:
    with open(('%s/seed.yaml' % os.path.abspath(output_dir)) , 'w') as outfile:
      yaml.dump(sim_seed, outfile, default_flow_style=False)
  if lsf_cmd:
    run_parallel_cmd(cmd_list, timeout_s, check_return_code = check_return_code)


def gen(test_list, cfg, output_dir, cwd):
  """Run the instruction generator

  Args:
    test_list             : List of assembly programs to be compiled
    cfg                   : Loaded configuration dictionary.
    output_dir            : Output directory of the ELF files
    cwd                   : Filesystem path to RISCV-DV repo
  """
  # Convert key dictionary to argv variable
  argv= SimpleNamespace(**cfg)

  check_return_code = True
  if argv.simulator == "ius":
    # Incisive return non-zero return code even test passes
    check_return_code = False
    logging.debug("Disable return_code checking for %s" % argv.simulator)
  # Mutually exclusive options between compile_only and sim_only
  if argv.co and argv.so:
    logging.error("argument -co is not allowed with argument -so")
    return
  if ((argv.co == 0) and (len(test_list) == 0)):
    return
  # Setup the compile and simulation command for the generator
  compile_cmd = []
  sim_cmd = ""
  compile_cmd, sim_cmd = get_generator_cmd(argv.simulator, argv.simulator_yaml, argv.cov, argv.exp);
  # Compile the instruction generator
  if not argv.so:
    do_compile(compile_cmd, test_list, argv.core_setting_dir, cwd, argv.user_extension_dir,
               argv.cmp_opts, output_dir)
  # Run the instruction generator
  if not argv.co:
    do_simulate(sim_cmd, test_list, cwd, argv.sim_opts, argv.seed_yaml, argv.seed, argv.csr_yaml,
                argv.isa, argv.end_signature_addr, argv.lsf_cmd, argv.gen_timeout, argv.log_suffix,
                argv.batch_size, output_dir, argv.verbose, check_return_code)


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
      if not os.path.isfile(asm):
        logging.error("Cannot find assembly test: %s\n", asm)
        sys.exit(RET_FAIL)
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
      run_cmd_output(cmd.split())
      # Convert the ELF to plain binary, used in RTL sim
      logging.info("Converting to %s" % binary)
      cmd = ("%s -O binary %s %s" % (get_env_var("RISCV_OBJCOPY"), elf, binary))
      run_cmd_output(cmd.split())


def run_assembly(asm_test, iss_yaml, isa, mabi, gcc_opts, iss_opts, output_dir,
                 setting_dir):
  """Run a directed assembly test with ISS

  Args:
    asm_test    : Assembly test file
    iss_yaml    : ISS configuration file in YAML format
    isa         : ISA variant passed to the ISS
    mabi        : MABI variant passed to GCC
    gcc_opts    : User-defined options for GCC compilation
    iss_opts    : Instruction set simulators
    output_dir  : Output directory of compiled test files
    setting_dir : Generator setting directory
  """
  if not asm_test.endswith(".S"):
    logging.error("%s is not an assembly .S file" % asm_test)
    return
  cwd = os.path.dirname(os.path.realpath(__file__))
  asm_test = os.path.expanduser(asm_test)
  report = ("%s/iss_regr.log" % output_dir).rstrip()
  asm = re.sub(r"^.*\/", "", asm_test)
  asm = re.sub(r"\.S$", "", asm)
  prefix = ("%s/directed_asm_tests/%s"  % (output_dir, asm))
  elf = prefix + ".o"
  binary = prefix + ".bin"
  iss_list = iss_opts.split(",")
  run_cmd("mkdir -p %s/directed_asm_tests" % output_dir)
  logging.info("Compiling assembly test : %s" % asm_test)

  # gcc compilation
  cmd = ("%s -static -mcmodel=medany \
         -fvisibility=hidden -nostdlib \
         -nostartfiles %s \
         -I%s/user_extension \
         -T%s/scripts/link.ld %s -o %s " % \
         (get_env_var("RISCV_GCC"), asm_test, cwd, cwd, gcc_opts, elf))
  cmd += (" -march=%s" % isa)
  cmd += (" -mabi=%s" % mabi)
  run_cmd_output(cmd.split())
  # Convert the ELF to plain binary, used in RTL sim
  logging.info("Converting to %s" % binary)
  cmd = ("%s -O binary %s %s" % (get_env_var("RISCV_OBJCOPY"), elf, binary))
  run_cmd_output(cmd.split())
  log_list = []
  # ISS simulation
  for iss in iss_list:
    run_cmd("mkdir -p %s/%s_sim" % (output_dir, iss))
    log = ("%s/%s_sim/%s.log" % (output_dir, iss, asm))
    log_list.append(log)
    base_cmd = parse_iss_yaml(iss, iss_yaml, isa, setting_dir)
    logging.info("[%0s] Running ISS simulation: %s" % (iss, elf))
    cmd = get_iss_cmd(base_cmd, elf, log)
    run_cmd(cmd, 10)
    logging.info("[%0s] Running ISS simulation: %s ...done" % (iss, elf))
  if len(iss_list) == 2:
    compare_iss_log(iss_list, log_list, report)

def run_assembly_from_dir(asm_test_dir, iss_yaml, isa, mabi, gcc_opts, iss,
                          output_dir, setting_dir):
  """Run a directed assembly test from a directory with spike

  Args:
    asm_test_dir    : Assembly test file directory
    iss_yaml        : ISS configuration file in YAML format
    isa             : ISA variant passed to the ISS
    mabi            : MABI variant passed to GCC
    gcc_opts        : User-defined options for GCC compilation
    iss             : Instruction set simulators
    output_dir      : Output directory of compiled test files
    setting_dir     : Generator setting directory
  """
  result = run_cmd("find %s -name \"*.S\"" % asm_test_dir)
  if result:
    asm_list = result.splitlines()
    logging.info("Found %0d assembly tests under %s" %
                 (len(asm_list), asm_test_dir))
    for asm_file in asm_list:
      run_assembly(asm_file, iss_yaml, isa, mabi, gcc_opts, iss, output_dir,
                   setting_dir)
      if "," in iss:
        report = ("%s/iss_regr.log" % output_dir).rstrip()
        save_regr_report(report)
  else:
    logging.error("No assembly test(*.S) found under %s" % asm_test_dir)

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
    run_cmd_output(["mkdir", "-p", log_dir])
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
          if iss == "ovpsim":
            run_cmd(cmd, timeout_s, check_return_code=False)
          else:
            run_cmd(cmd, timeout_s)
          logging.debug(cmd)


def iss_cmp(test_list, iss, output_dir, stop_on_first_error, exp):
  """Compare ISS simulation reult

  Args:
    test_list      : List of assembly programs to be compiled
    iss            : List of instruction set simulators
    output_dir     : Output directory of the ELF files
    stop_on_first_error : will end run on first error detected
    exp            : Use experimental version
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
      log_list = []
      run_cmd(("echo 'Test binary: %s' >> %s" % (elf, report)))
      for iss in iss_list:
        log_list.append("%s/%s_sim/%s.%d.log" % (output_dir, iss, test['test'], i))
      compare_iss_log(iss_list, log_list, report, stop_on_first_error, exp)
  save_regr_report(report)

def compare_iss_log(iss_list, log_list, report, stop_on_first_error=0, exp=False):
  if (len(iss_list) != 2 or len(log_list) != 2) :
    logging.error("Only support comparing two ISS logs")
  else:
    csv_list = []
    for i in range(2):
      log = log_list[i]
      csv = log.replace(".log", ".csv");
      iss = iss_list[i]
      csv_list.append(csv)
      if iss == "spike":
        process_spike_sim_log(log, csv)
      elif iss == "ovpsim":
        process_ovpsim_sim_log(log, csv, stop_on_first_error)
      elif iss == "sail":
        process_sail_sim_log(log, csv)
      elif iss == "whisper":
        process_whisper_sim_log(log, csv)
      else:
        logging.error("Unsupported ISS" % iss)
        sys.exit(RET_FAIL)
    result = compare_trace_csv(csv_list[0], csv_list[1], iss_list[0], iss_list[1], report)
    logging.info(result)


def save_regr_report(report):
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
  parser.add_argument("-v", "--verbose", dest="verbose", action="store_true", default=False,
                      help="Verbose logging")
  parser.add_argument("--co", dest="co", action="store_true", default=False,
                      help="Compile the generator only")
  parser.add_argument("--cov", dest="cov", action="store_true", default=False,
                      help="Enable functional coverage")
  parser.add_argument("--so", dest="so", action="store_true", default=False,
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
  parser.add_argument("--asm_tests", type=str, default="",
                      help="Directed assembly tests")
  parser.add_argument("--log_suffix", type=str, default="",
                      help="Simulation log name suffix")
  parser.add_argument("--exp", action="store_true", default=False,
                      help="Run generator with experimental features")
  parser.add_argument("-bz", "--batch_size", type=int, default=0,
                      help="Number of tests to generate per run. You can split a big"
                           " job to small batches with this option")
  parser.add_argument("--stop_on_first_error", dest="stop_on_first_error",
                      action="store_true", default=False,
                      help="Stop on detecting first error")
  parser.add_argument("--noclean", action="store_true", default=True,
                      help="Do not clean the output of the previous runs")
  return parser

def load_config(args, cwd):
  """
  Load configuration from the command line and the configuration file.
  Args:
      args:   Parsed command-line configuration
  Returns:
      Loaded configuration dictionary.
  """
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
    elif args.target == "rv64gcv":
      args.mabi = "lp64"
      args.isa  = "rv64gcv"
    elif args.target == "ml":
      args.mabi = "lp64"
      args.isa  = "rv64imc"
    else:
      sys.exit("Unsupported pre-defined target: %0s" % args.target)
  else:
    if re.match(".*gcc_compile.*", args.steps) or re.match(".*iss_sim.*", args.steps):
      if (not args.mabi) or (not args.isa):
        sys.exit("mabi and isa must be specified for custom target %0s" % args.custom_target)
    if not args.testlist:
      args.testlist = args.custom_target + "/testlist.yaml"
  # Create loaded configuration dictionary.
  cfg = vars(args)
  return cfg

def main():
  """This is the main entry point."""
  try:
    parser = setup_parser()
    args = parser.parse_args()
    cwd = os.path.dirname(os.path.realpath(__file__))
    os.environ["RISCV_DV_ROOT"] = cwd
    setup_logging(args.verbose)
    # Load configuration from the command line and the configuration file.
    cfg = load_config(args, cwd)
    # Create output directory
    output_dir = create_output(args.o, args.noclean)

    # Run any handcoded/directed assembly tests specified by args.asm_tests
    if args.asm_tests != "":
      asm_test = args.asm_tests.split(',')
      for path_asm_test in asm_test:
        full_path = os.path.expanduser(path_asm_test)
        # path_asm_test is a directory
        if os.path.isdir(full_path):
          run_assembly_from_dir(full_path, args.iss_yaml, args.isa, args.mabi,
                                args.gcc_opts, args.iss, output_dir, args.core_setting_dir)
        # path_asm_test is an assembly file
        elif os.path.isfile(full_path):
          run_assembly(full_path, args.iss_yaml, args.isa, args.mabi, args.gcc_opts,
                       args.iss, output_dir, args.core_setting_dir)
        else:
          logging.error('%s does not exist' % full_path)
          sys.exit(RET_FAIL)
      return

    run_cmd_output(["mkdir", "-p", ("%s/asm_tests" % output_dir)])
    # Process regression test list
    matched_list = []
    # Any tests in the YAML test list that specify a directed assembly test
    directed_list = []

    if not args.co:
      process_regression_list(args.testlist, args.test, args.iterations, matched_list, cwd)
      for t in list(matched_list):
        if 'asm_tests' in t:
          if 'gen_test' in t:
            logging.error('asm_test must not be defined in the testlist '
                          'together with the gen_test field')
            sys.exit(RET_FATAL)
          directed_list.append(t)
          matched_list.remove(t)

      if len(matched_list) == 0 and len(directed_list) == 0:
        sys.exit("Cannot find %s in %s" % (args.test, args.testlist))

    # Run instruction generator
    if args.steps == "all" or re.match(".*gen.*", args.steps):
      # Run any handcoded/directed assembly tests specified in YAML format
      if len(directed_list) != 0:
        for test_entry in directed_list:
          gcc_opts = args.gcc_opts
          gcc_opts += test_entry.get('gcc_opts', '')
          path_asm_test = os.path.expanduser(test_entry.get('asm_tests'))
          if path_asm_test:
            # path_asm_test is a directory
            if os.path.isdir(path_asm_test):
              run_assembly_from_dir(path_asm_test, args.iss_yaml, args.isa, args.mabi,
                                    gcc_opts, args.iss, output_dir, args.core_setting_dir)
            # path_asm_test is an assembly file
            elif os.path.isfile(path_asm_test):
              run_assembly(path_asm_test, args.iss_yaml, args.isa, args.mabi, gcc_opts,
                           args.iss, output_dir, args.core_setting_dir)
            else:
              logging.error('%s does not exist' % path_asm_test)
              sys.exit(RET_FAIL)
      # Run remaining tests using the instruction generator
      gen(matched_list, cfg, output_dir, cwd)

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
        iss_cmp(matched_list, args.iss, output_dir, args.stop_on_first_error, args.exp)

    sys.exit(RET_SUCCESS)
  except KeyboardInterrupt:
    logging.info("\nExited Ctrl-C from user request.")
    sys.exit(130)

if __name__ == "__main__":
  main()
