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

Convert sail sim log to standard riscv instruction trace format
"""

import argparse
import os
import re
import sys
import logging

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *

START_RE = re.compile(r"\[4\] \[M\]: 0x.*00001010")
END_RE = re.compile(r"ecall")
INSTR_RE = re.compile(r"\[[0-9].*\] \[(?P<pri>.)\]: 0x(?P<addr>[A-F0-9]+?)"
                      " \(0x(?P<bin>[A-F0-9]+?)\) (?P<instr>.+?$)")
RD_RE = re.compile(r"x(?P<reg>[0-9]+?) <- 0x(?P<val>[A-F0-9]*)")


def process_sail_sim_log(sail_log, csv):
    """Process SAIL RISCV simulation log.

    Extract instruction and affected register information from sail simulation
    log and save to a list.
    """
    logging.info("Processing sail log : {}".format(sail_log))
    instr_cnt = 0

    with open(sail_log, "r") as f, open(csv, "w") as csv_fd:
        search_start = 0
        instr_start = 0
        trace_csv = RiscvInstructionTraceCsv(csv_fd)
        trace_csv.start_new_trace()
        instr = None
        for line in f:
            # Extract instruction infromation
            m = START_RE.search(line)
            if m:
                search_start = 1
                continue
            m = END_RE.search(line)
            if m:
                break
            if search_start:
                instr = INSTR_RE.search(line)
                if instr:
                    instr_start = 1
                    pri = instr.group("pri")
                    addr = instr.group("addr").lower()
                    binary = instr.group("bin").lower()
                    instr_str = instr.group("instr")
                    continue
                if instr_start:
                    m = RD_RE.search(line)
                    if m:
                        # Write the extracted instruction to a csvcol buffer file
                        instr_cnt += 1
                        rv_instr_trace = RiscvInstructionTraceEntry()
                        rv_instr_trace.gpr.append(
                            gpr_to_abi("x{}".format(m.group("reg"))) + ":" + m.group(
                                "val").lower())
                        rv_instr_trace.mode = pri
                        rv_instr_trace.pc = addr
                        rv_instr_trace.binary = binary
                        rv_instr_trace.instr_str = instr_str
                        trace_csv.write_trace_entry(rv_instr_trace)
                        instr_start = 0
    logging.info("Processed instruction count : {}".format(instr_cnt))


def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=str, help="Input sail simulation log")
    parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
    args = parser.parse_args()
    # Process sail log
    process_sail_sim_log(args.log, args.csv)


if __name__ == "__main__":
    main()
