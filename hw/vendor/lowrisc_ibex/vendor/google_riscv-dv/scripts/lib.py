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

Parse the regression testlist in YAML format
"""

import os
import random
import sys
import re
import subprocess
import time
import yaml
import logging

from datetime import date

RET_SUCCESS = 0
RET_FAIL    = 1
RET_FATAL   = -1


def setup_logging(verbose):
    """Setup the root logger.

    Args:
      verbose: Verbose logging
    """
    if verbose:
        logging.basicConfig(
            format="%(asctime)s %(filename)s:%(lineno)-5s %(levelname)-8s %(message)s",
            datefmt='%a, %d %b %Y %H:%M:%S',
            level=logging.DEBUG)
    else:
        logging.basicConfig(format="%(asctime)s %(levelname)-8s %(message)s",
                            datefmt='%a, %d %b %Y %H:%M:%S',
                            level=logging.INFO)


def read_yaml(yaml_file):
    """ Read YAML file to a dictionary

    Args:
      yaml_file : YAML file

    Returns:
      yaml_data : data read from YAML in dictionary format
    """
    with open(yaml_file, "r") as f:
        try:
            yaml_data = yaml.safe_load(f)
        except yaml.YAMLError as exc:
            logging.error(exc)
            sys.exit(RET_FAIL)
    return yaml_data


def get_env_var(var, debug_cmd=None):
    """Get the value of environment variable

    Args:
      var : Name of the environment variable

    Returns:
      val : Value of the environment variable
    """
    try:
        val = os.environ[var]
    except KeyError:
        if debug_cmd:
            return var
        else:
            logging.warning("Please set the environment variable {}".format(var))
            sys.exit(RET_FAIL)
    return val


def run_cmd(cmd, timeout_s=999, exit_on_error=1, check_return_code=True,
            debug_cmd=None):
    """Run a command and return output

    Args:
      cmd : shell command to run

    Returns:
      command output
    """
    logging.debug(cmd)
    if debug_cmd:
        debug_cmd.write(cmd)
        debug_cmd.write("\n\n")
        return
    try:
        ps = subprocess.Popen("exec " + cmd,
                              shell=True,
                              executable='/bin/bash',
                              universal_newlines=True,
                              stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError:
        logging.error(ps.communicate()[0])
        sys.exit(RET_FAIL)
    except KeyboardInterrupt:
        logging.info("\nExited Ctrl-C from user request.")
        sys.exit(130)
    try:
        output = ps.communicate(timeout=timeout_s)[0]
    except subprocess.TimeoutExpired:
        logging.error("Timeout[{}s]: {}".format(timeout_s, cmd))
        output = ""
        ps.kill()
    rc = ps.returncode
    if rc and check_return_code and rc > 0:
        logging.info(output)
        logging.error(
            "ERROR return code: {}/{}, cmd:{}".format(check_return_code, rc, cmd))
        if exit_on_error:
            sys.exit(RET_FAIL)
    logging.debug(output)
    return output


def run_parallel_cmd(cmd_list, timeout_s=999, exit_on_error=0,
                     check_return_code=True, debug_cmd=None):
    """Run a list of commands in parallel

    Args:
      cmd_list: command list

    Returns:
      command output
    """
    if debug_cmd:
        for cmd in cmd_list:
            debug_cmd.write(cmd)
            debug_cmd.write("\n\n")
        return
    children = []
    for cmd in cmd_list:
        ps = subprocess.Popen("exec " + cmd,
                              shell=True,
                              executable='/bin/bash',
                              universal_newlines=True,
                              stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
        children.append(ps)
    for i in range(len(children)):
        logging.info("Command progress: {}/{}".format(i, len(children)))
        logging.debug("Waiting for command: {}".format(cmd_list[i]))
        try:
            output = children[i].communicate(timeout=timeout_s)[0]
        except KeyboardInterrupt:
            logging.info("\nExited Ctrl-C from user request.")
            sys.exit(130)
        except subprocess.TimeoutExpired:
            logging.error("Timeout[{}s]: {}".format(timeout_s, cmd))
            children[i].kill()
        rc = children[i].returncode
        if rc and check_return_code and rc > 0:
            logging.info(output)
            logging.error("ERROR return code: {}, cmd:{}".format(rc, cmd))
            if exit_on_error:
                sys.exit(RET_FAIL)
        # Restore stty setting otherwise the terminal may go crazy
        os.system("stty sane")
        logging.debug(output)


def run_cmd_output(cmd, debug_cmd=None):
    """Run a command and return output
    Args:
      cmd          : Command line to execute
    """
    logging.debug(" ".join(cmd))
    if debug_cmd:
        debug_cmd.write(" ".join(cmd))
        debug_cmd.write("\n\n")
        return
    try:
        output = subprocess.check_output(cmd)
    except subprocess.CalledProcessError as exc:
        logging.debug(exc.output)
        raise exc
        sys.exit(RET_FAIL)
    if output:
        logging.debug(output)


def process_regression_list(testlist, test, iterations, matched_list,
                            riscv_dv_root):
    """ Get the matched tests from the regression test list

    Args:
      testlist      : Regression test list
      test          : Test to run, "all" means all tests in the list
      iterations    : Number of iterations for each test
      riscv_dv_root : Root directory of RISCV-DV

    Returns:
      matched_list : A list of matched tests
    """
    logging.info(
        "Processing regression test list : {}, test: {}".format(testlist, test))
    yaml_data = read_yaml(testlist)
    mult_test = test.split(',')
    for entry in yaml_data:
        if 'import' in entry:
            sub_list = re.sub('<riscv_dv_root>', riscv_dv_root, entry['import'])
            process_regression_list(sub_list, test, iterations, matched_list,
                                    riscv_dv_root)
        else:
            if (entry['test'] in mult_test) or (test == "all"):
                if iterations > 0 and entry['iterations'] > 0:
                    entry['iterations'] = iterations
                if entry['iterations'] > 0:
                    logging.info("Found matched tests: {}, iterations:{}".format(
                      entry['test'], entry['iterations']))
                    matched_list.append(entry)


def create_output(output, noclean, prefix="out_"):
    """ Create output directory

  Args:
    output : Name of specified output directory
    noclean: Do not clean the output of the previous runs

  Returns:
    Output directory
  """
    # Create output directory
    if output is None:
        output = prefix + str(date.today())
    if noclean is False:
        os.system("rm -rf {}".format(output))

    logging.info("Creating output directory: {}".format(output))
    subprocess.run(["mkdir", "-p", output])
    return output


def gpr_to_abi(gpr):
    """Convert a general purpose register to its corresponding abi name"""
    switcher = {
        "x0" : "zero",
        "x1" : "ra",
        "x2" : "sp",
        "x3" : "gp",
        "x4" : "tp",
        "x5" : "t0",
        "x6" : "t1",
        "x7" : "t2",
        "x8" : "s0",
        "x9" : "s1",
        "x10": "a0",
        "x11": "a1",
        "x12": "a2",
        "x13": "a3",
        "x14": "a4",
        "x15": "a5",
        "x16": "a6",
        "x17": "a7",
        "x18": "s2",
        "x19": "s3",
        "x20": "s4",
        "x21": "s5",
        "x22": "s6",
        "x23": "s7",
        "x24": "s8",
        "x25": "s9",
        "x26": "s10",
        "x27": "s11",
        "x28": "t3",
        "x29": "t4",
        "x30": "t5",
        "x31": "t6",
        "f0" : "ft0",
        "f1" : "ft1",
        "f2" : "ft2",
        "f3" : "ft3",
        "f4" : "ft4",
        "f5" : "ft5",
        "f6" : "ft6",
        "f7" : "ft7",
        "f8" : "fs0",
        "f9" : "fs1",
        "f10": "fa0",
        "f11": "fa1",
        "f12": "fa2",
        "f13": "fa3",
        "f14": "fa4",
        "f15": "fa5",
        "f16": "fa6",
        "f17": "fa7",
        "f18": "fs2",
        "f19": "fs3",
        "f20": "fs4",
        "f21": "fs5",
        "f22": "fs6",
        "f23": "fs7",
        "f24": "fs8",
        "f25": "fs9",
        "f26": "fs10",
        "f27": "fs11",
        "f28": "ft8",
        "f29": "ft9",
        "f30": "ft10",
        "f31": "ft11",
    }
    return switcher.get(gpr, "na")


def sint_to_hex(val):
    """Signed integer to hex conversion"""
    return str(hex((val + (1 << 32)) % (1 << 32)))


BASE_RE = re.compile(
    r"(?P<rd>[a-z0-9]+?),(?P<imm>[\-0-9]*?)\((?P<rs1>[a-z0-9]+?)\)")


def convert_pseudo_instr(instr_name, operands, binary):
    """Convert pseudo instruction to regular instruction"""
    if instr_name == "nop":
        instr_name = "addi"
        operands = "zero,zero,0"
    elif instr_name == "mv":
        instr_name = "addi"
        operands = operands + ",0"
    elif instr_name == "not":
        instr_name = "xori"
        operands = operands + ",-1"
    elif instr_name == "neg":
        instr_name = "sub"
        o = operands.split(",")
        operands = o[0] + ",zero," + o[1]
    elif instr_name == "negw":
        instr_name = "subw"
        o = operands.split(",")
        operands = o[0] + ",zero," + o[1]
    elif instr_name == "sext.w":
        instr_name = "addiw"
        operands = operands + ",0"
    elif instr_name == "seqz":
        instr_name = "sltiu"
        operands = operands + ",1"
    elif instr_name == "snez":
        instr_name = "sltu"
        o = operands.split(",")
        operands = o[0] + ",zero," + o[1]
    elif instr_name == "sltz":
        instr_name = "slt"
        operands = operands + ",zero"
    elif instr_name == "sgtz":
        instr_name = "slt"
        o = operands.split(",")
        operands = o[0] + ",zero," + o[1]
    elif instr_name in ["beqz", "bnez", "bgez", "bltz"]:
        instr_name = instr_name[0:3]
        o = operands.split(",")
        operands = o[0] + ",zero," + o[1]
    elif instr_name == "blez":
        instr_name = "bge"
        operands = "zero," + operands
    elif instr_name == "bgtz":
        instr_name = "blt"
        operands = "zero," + operands
    elif instr_name == "bgt":
        instr_name = "blt"
        o = operands.split(",")
        operands = o[1] + "," + o[0] + "," + o[2]
    elif instr_name == "ble":
        instr_name = "bge"
        o = operands.split(",")
        operands = o[1] + "," + o[0] + "," + o[2]
    elif instr_name == "bgtu":
        instr_name = "bltu"
        o = operands.split(",")
        operands = o[1] + "," + o[0] + "," + o[2]
    elif instr_name == "bleu":
        instr_name = "bgeu"
        o = operands.split(",")
        operands = o[1] + "," + o[0] + "," + o[2]
    elif instr_name == "csrr":
        instr_name = "csrrw"
        operands = operands + ",zero"
    elif instr_name in ["csrw", "csrs", "csrc"]:
        instr_name = "csrr" + instr_name[3:]
        operands = "zero," + operands
    elif instr_name in ["csrwi", "csrsi", "csrci"]:
        instr_name = "csrr" + instr_name[3:]
        operands = "zero," + operands
    elif instr_name == "jr":
        instr_name = "jalr"
        operands = "zero,{},0".format(operands)
    elif instr_name == "j":
        instr_name = "jal"
        operands = "zero,{}".format(operands)
    elif instr_name == "jal":
        if not ("," in operands):
            operands = "ra,{}".format(operands)
    elif instr_name == "jalr":
        m = BASE_RE.search(operands)
        # jalr rd, imm(rs1)
        if m:
            operands = "{},{},{}".format(m.group("rd"), m.group("rs1"), m.group("imm"))
        # jalr rs1
        idx = operands.rfind(",")
        if idx == -1:
            operands = "ra," + operands + ",0"
    elif instr_name == "ret":
        if binary[-1] == "2":
            instr_name = "c.jr"
            operands = "ra"
        else:
            instr_name = "jalr"
            operands = "zero,ra,0"
    # RV32B pseudo instructions
    # TODO: support "rev", "orc", and "zip/unzip" instructions for RV64
    elif instr_name == "rev.p":
        instr_name = "grevi"
        operands += ",1"
    elif instr_name == "rev2.n":
        instr_name = "grevi"
        operands += ",2"
    elif instr_name == "rev.n":
        instr_name = "grevi"
        operands += ",3"
    elif instr_name == "rev4.b":
        instr_name = "grevi"
        operands += ",4"
    elif instr_name == "rev2.b":
        instr_name = "grevi"
        operands += ",6"
    elif instr_name == "rev.b":
        instr_name = "grevi"
        operands += ",7"
    elif instr_name == "rev8.h":
        instr_name = "grevi"
        operands += ",8"
    elif instr_name == "rev4.h":
        instr_name = "grevi"
        operands += ",12"
    elif instr_name == "rev2.h":
        instr_name = "grevi"
        operands += ",14"
    elif instr_name == "rev.h":
        instr_name = "grevi"
        operands += ",15"
    elif instr_name == "rev16":
        instr_name = "grevi"
        operands += ",16"
    elif instr_name == "rev8":
        instr_name = "grevi"
        operands += ",24"
    elif instr_name == "rev4":
        instr_name = "grevi"
        operands += ",28"
    elif instr_name == "rev2":
        instr_name = "grevi"
        operands += ",30"
    elif instr_name == "rev":
        instr_name = "grevi"
        operands += ",31"
    elif instr_name == "orc.p":
        instr_name = "gorci"
        operands += ",1"
    elif instr_name == "orc2.n":
        instr_name = "gorci"
        operands += ",2"
    elif instr_name == "orc.n":
        instr_name = "gorci"
        operands += ",3"
    elif instr_name == "orc4.b":
        instr_name = "gorci"
        operands += ",4"
    elif instr_name == "orc2.b":
        instr_name = "gorci"
        operands += ",6"
    elif instr_name == "orc.b":
        instr_name = "gorci"
        operands += ",7"
    elif instr_name == "orc8.h":
        instr_name = "gorci"
        operands += ",8"
    elif instr_name == "orc4.h":
        instr_name = "gorci"
        operands += ",12"
    elif instr_name == "orc2.h":
        instr_name = "gorci"
        operands += ",14"
    elif instr_name == "orc.h":
        instr_name = "gorci"
        operands += ",15"
    elif instr_name == "orc16":
        instr_name = "gorci"
        operands += ",16"
    elif instr_name == "orc8":
        instr_name = "gorci"
        operands += ",24"
    elif instr_name == "orc4":
        instr_name = "gorci"
        operands += ",28"
    elif instr_name == "orc2":
        instr_name = "gorci"
        operands += ",30"
    elif instr_name == "orc":
        instr_name = "gorci"
        operands += ",31"
    elif instr_name == "zext.b":
        instr_name = "andi"
        operands += ",255"
    elif instr_name == "zext.h":
        # TODO: support for RV64B
        instr_name = "pack"
        operands += ",zero"
    elif instr_name == "zext.w":
        instr_name = "pack"
        operands += ",zero"
    elif instr_name == "sext.w":
        instr_name = "addiw"
        operands += ",0"
    elif instr_name == "zip.n":
        instr_name = "shfli"
        operands += ",1"
    elif instr_name == "unzip.n":
        instr_name = "unshfli"
        operands += ",1"
    elif instr_name == "zip2.b":
        instr_name = "shfli"
        operands += ",2"
    elif instr_name == "unzip2.b":
        instr_name = "unshfli"
        operands += ",2"
    elif instr_name == "zip.b":
        instr_name = "shfli"
        operands += ",3"
    elif instr_name == "unzip.b":
        instr_name = "unshfli"
        operands += ",3"
    elif instr_name == "zip4.h":
        instr_name = "shfli"
        operands += ",4"
    elif instr_name == "unzip4.h":
        instr_name = "unshfli"
        operands += ",4"
    elif instr_name == "zip2.h":
        instr_name = "shfli"
        operands += ",6"
    elif instr_name == "unzip2.h":
        instr_name = "unshfli"
        operands += ",6"
    elif instr_name == "zip.h":
        instr_name = "shfli"
        operands += ",7"
    elif instr_name == "unzip.h":
        instr_name = "unshfli"
        operands += ",7"
    elif instr_name == "zip8":
        instr_name = "shfli"
        operands += ",8"
    elif instr_name == "unzip8":
        instr_name = "unshfli"
        operands += ",8"
    elif instr_name == "zip4":
        instr_name = "shfli"
        operands += ",12"
    elif instr_name == "unzip4":
        instr_name = "unshfli"
        operands += ",12"
    elif instr_name == "zip2":
        instr_name = "shfli"
        operands += ",14"
    elif instr_name == "unzip2":
        instr_name = "unshfli"
        operands += ",14"
    elif instr_name == "zip":
        instr_name = "shfli"
        operands += ",15"
    elif instr_name == "unzip":
        instr_name = "unshfli"
        operands += ",15"
    return instr_name, operands
