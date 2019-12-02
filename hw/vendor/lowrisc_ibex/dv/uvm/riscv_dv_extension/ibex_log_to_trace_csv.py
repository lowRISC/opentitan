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

REGS = ["zero","ra","sp","gp","tp","t0","t1","t2","s0","s1",
        "a0","a1","a2","a3","a4","a5","a6","a7",
        "s2","s3","s4","s5","s6","s7","s8","s9","s10","s11",
        "t3","t4","t5","t6"]

def process_ibex_sim_log(ibex_log, csv, full_trace = 1):
    """Process ibex simulation log.

    Extract instruction and affected register information from ibex simulation
    log and save to a standard CSV format.
    """
    logging.info("Processing ibex log : %s" % ibex_log)
    instr_cnt = 0
    ibex_instr = ""

    gpr = {}
    for g in REGS:
      gpr[g] = 0

    with open(ibex_log, "r") as f, open(csv, "w") as csv_fd:
        trace_csv = RiscvInstructionTraceCsv(csv_fd)
        trace_csv.start_new_trace()
        for line in f:
            if re.search("ecall", line):
              break
            # Extract instruction information
            m = re.search(r"^\s*(?P<time>\d+)\s+" \
                          "(?P<cycle>\d+)\s+" \
                          "(?P<pc>[0-9a-f]+)\s+" \
                          "(?P<bin>[0-9a-f]+)\s+" \
                          "(?P<instr>\S+\s+\S+)\s*" \
                          "(x(?P<rs1>\d+):0x(?P<rs1_val>[0-9a-f]+))?\s*" \
                          "(x(?P<rs2>\d+):0x(?P<rs2_val>[0-9a-f]+))?\s*" \
                          "(x(?P<rd>[1-9]\d*)=0x(?P<rd_val>[0-9a-f]+))", line)
            if m:
                instr_cnt += 1
                # Write the extracted instruction to a csvcol buffer file
                rv_instr_trace = RiscvInstructionTraceEntry()
                rv_instr_trace.rd = gpr_to_abi("x%0s" % m.group("rd"))
                rv_instr_trace.rd_val = m.group("rd_val")
                rv_instr_trace.rs1 = gpr_to_abi("x%0s" % m.group("rs1"))
                rv_instr_trace.rs1_val = m.group("rs1_val")
                rv_instr_trace.rs2 = gpr_to_abi("x%0s" % m.group("rs2"))
                rv_instr_trace.rs2_val = m.group("rs2_val")
                rv_instr_trace.addr = m.group("pc")
                rv_instr_trace.binary = m.group("bin")
                rv_instr_trace.instr_str = m.group("instr")
                rv_instr_trace.instr = rv_instr_trace.instr_str.split()[0]

                # Extract all missing operand values
                if full_trace:
                  gpr[rv_instr_trace.rd] = rv_instr_trace.rd_val
                  o = re.search(r"(?P<instr_name>[a-z.]*)\s+(?P<operands>.*)", rv_instr_trace.instr_str)
                  if o:
                    operands = o.group("operands").split(",")
                    # Convert to ABI representation
                    for i in range(len(operands)):
                      abi = re.search(r"(^|\()(?P<gpr>x\d+)", operands[i])
                      if abi:
                        reg = abi.group("gpr")
                        operands[i] = operands[i].replace(reg, gpr_to_abi(reg))
                    if rv_instr_trace.instr in ['jalr']:
                      # Ibex displays two operands for jalr
                      rv_instr_trace.rd = operands[0]
                      rv_instr_trace.rd_val = gpr[rv_instr_trace.rd]
                      n = ADDR_RE.search(operands[1])
                      if n:
                        rv_instr_trace.rs1 = n.group("rs1")
                        rv_instr_trace.rs1_val = gpr[rv_instr_trace.rs1]
                        rv_instr_trace.imm = get_imm_hex_val(n.group("imm"))
                    elif rv_instr_trace.instr in ['c.jal']:
                      rv_instr_trace.imm = get_imm_hex_val("0x" + operands[0])
                    elif rv_instr_trace.instr in ['jal']:
                      rv_instr_trace.rd = operands[0]
                      rv_instr_trace.rd_val = gpr[rv_instr_trace.rd]
                      rv_instr_trace.imm = get_imm_hex_val("0x" + operands[1])
                    else:
                      assign_operand(rv_instr_trace, operands, gpr)

                trace_csv.write_trace_entry(rv_instr_trace)

    logging.info("Processed instruction count : %d" % instr_cnt)


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
