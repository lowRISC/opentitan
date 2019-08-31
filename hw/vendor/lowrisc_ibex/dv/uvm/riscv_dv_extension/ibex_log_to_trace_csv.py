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


def process_ibex_sim_log(ibex_log, csv):
    """Process ibex simulation log.

    Extract instruction and affected register information from ibex simulation
    log and save to a standard CSV format.
    """
    print("Processing ibex log : %s" % ibex_log)
    instr_cnt = 0
    ibex_instr = ""

    with open(ibex_log, "r") as f, open(csv, "w") as csv_fd:
        trace_csv = RiscvInstructiontTraceCsv(csv_fd)
        trace_csv.start_new_trace()
        for line in f:
            # Extract instruction infromation
            m = re.search(r"^\s*(?P<time>\d+)\s+(?P<cycle>\d+) " \
                          "(?P<pc>[0-9a-f]+) (?P<bin>[0-9a-f]+) (?P<instr>.*)" \
                          "x(?P<rd>\d+)=0x(?P<val>[0-9a-f]+)", line)
            if m:
                # Write the extracted instruction to a csvcol buffer file
                rv_instr_trace = RiscvInstructiontTraceEntry()
                rv_instr_trace.rd = gpr_to_abi("x%0s" % m.group("rd"))
                rv_instr_trace.rd_val = m.group("val")
                rv_instr_trace.addr = m.group("pc")
                rv_instr_trace.binary = m.group("bin")
                rv_instr_trace.instr_str = m.group("instr")
                trace_csv.write_trace_entry(rv_instr_trace)
                instr_cnt += 1

    print("Processed instruction count : %d" % instr_cnt)


def main():
  instr_trace = []
  # Parse input arguments
  parser = argparse.ArgumentParser()
  parser.add_argument("--log", type=str, help="Input ibex simulation log")
  parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
  args = parser.parse_args()
  # Process ibex log
  process_ibex_sim_log(args.log, args.csv)


if __name__ == "__main__":
  main()
