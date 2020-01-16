# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Convert ibex log to the standard trace CSV format

import argparse
import re
import sys

sys.path.insert(0, "../../vendor/google_riscv-dv/scripts")

from riscv_trace_csv import *
from lib import *


INSTR_RE = re.compile(r"^\s*(?P<time>\d+)\s+(?P<cycle>\d+)\s+(?P<pc>[0-9a-f]+)\s+" \
                      "(?P<bin>[0-9a-f]+)\s+(?P<instr>\S+\s+\S+)\s*")
RD_RE = re.compile(r"(x(?P<rd>[1-9]\d*)=0x(?P<rd_val>[0-9a-f]+))")
ADDR_RE  = re.compile(r"(?P<imm>[\-0-9]+?)\((?P<rs1>.*)\)")


def process_ibex_sim_log(ibex_log, csv, full_trace = 1):
  """Process ibex simulation log.

  Extract instruction and affected register information from ibex simulation
  log and save to a standard CSV format.
  """
  logging.info("Processing ibex log : %s" % ibex_log)
  instr_cnt = 0
  ibex_instr = ""

  with open(ibex_log, "r") as f, open(csv, "w") as csv_fd:
    trace_csv = RiscvInstructionTraceCsv(csv_fd)
    trace_csv.start_new_trace()
    for line in f:
      if re.search("ecall", line):
        break
      # Extract instruction information
      m = INSTR_RE.search(line)
      if m:
        instr_cnt += 1
        # Write the extracted instruction to a csvcol buffer file
        rv_instr_trace = RiscvInstructionTraceEntry()
        rv_instr_trace.instr_str = m.group("instr")
        rv_instr_trace.instr = m.group("instr").split()[0]
        rv_instr_trace.pc = m.group("pc")
        rv_instr_trace.binary = m.group("bin")
        if full_trace:
          rv_instr_trace.operand = m.group("instr").split()[1]
          process_trace(rv_instr_trace)
      c = RD_RE.search(line)
      if c:
        rv_instr_trace.gpr.append(gpr_to_abi("x%0s" % c.group("rd")) + ":" + c.group("rd_val"))
        trace_csv.write_trace_entry(rv_instr_trace)

  logging.info("Processed instruction count : %d" % instr_cnt)
  if instr_cnt == 0:
    logging.error("No instructions in logfile: %s" % ibex_log)
    sys.exit(RET_FATAL)
  logging.info("CSV saved to : %s" % csv)


def process_trace(trace):
  """ Process instruction trace """
  process_imm(trace)
  if trace.instr == 'jalr':
    n = ADDR_RE.search(trace.operand)
    if n:
      trace.imm = get_imm_hex_val(n.group("imm"))


def process_imm(trace):
  """ Process imm to follow RISC-V standard convention """
  if trace.instr in ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'c.beqz',
                     'c.bnez', 'beqz', 'bnez', 'bgez', 'bltz', 'blez', 'bgtz',
                     'c.j', 'j', 'c.jal', 'jal']:
    idx = trace.operand.rfind(',')
    if idx == -1:
      imm = trace.operand
      imm = str(sint_to_hex(int(imm, 16) - int(trace.pc, 16)))
      trace.operand = imm
    else:
      imm = trace.operand[idx + 1 : ]
      imm = str(sint_to_hex(int(imm, 16) - int(trace.pc, 16)))
      trace.operand = trace.operand[0 : idx + 1] + imm


def check_ibex_uvm_log(uvm_log, core_name, test_name, report, write=True):
  """Process Ibex UVM simulation log.

  This function will be used when a test disables the normal post_compare step.
  Process the UVM simulation log produced by the test to check for correctness

  Args:
    uvm_log: the uvm simulation log
    core_name: the name of the core
    test_name: name of the test being checked
    report: the output report file
    write: enables writing to the log file

  Returns:
    A boolean indicating whether the test passed or failed based on the signature
  """
  pass_cnt = 0
  fail_cnt = 0
  with open(uvm_log, "r") as log:
    for line in log:
      if 'RISC-V UVM TEST PASSED' in line:
        pass_cnt += 1
        break
      elif 'RISC-V UVM TEST FAILED' in line:
        fail_cnt += 1
        break

  if write:
    if report:
      fd = open(report, "a+")
    else:
      fd = sys.stdout
    fd.write("%s uvm log : %s\n" % (core_name, uvm_log))
    if pass_cnt == 1:
      fd.write("%s : [PASSED]\n\n" % test_name)
    elif fail_cnt == 1:
      fd.write("%s : [FAILED]\n\n" % test_name)
    if report:
      fd.close()

  return pass_cnt == 1


def main():
  instr_trace = []
  # Parse input arguments
  parser = argparse.ArgumentParser()
  parser.add_argument("--log", type=str, help="Input ibex simulation log")
  parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
  parser.add_argument("--full_trace", type=int, default=1,
                      help="Enable full log trace")
  args = parser.parse_args()
  # Process ibex log
  process_ibex_sim_log(args.log, args.csv, args.full_trace)


if __name__ == "__main__":
  main()
