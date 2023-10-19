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

Convert whisper sim log to standard riscv instruction trace format
"""

import argparse
import os
import re
import sys
import logging

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *
from lib import *

INSTR_RE = re.compile(
    r"#(?P<n>[0-9]+?)\s+(?P<mode>[0-9]+?)\s+(?P<pc>[0-9a-f]+?)\s+" \
    "(?P<bin>[0-9a-f]+?)\s+(?P<type>[a-z]+?)\s+" \
    "(?P<reg>[0-9a-f]+?)\s+(?P<val>[0-9a-f]+?)\s+(?P<instr>.*?)$")

LOGGER = logging.getLogger()


def process_whisper_sim_log(whisper_log, csv, full_trace=0):
    """Process SPIKE simulation log.

    Extract instruction and affected register information from whisper simulation
    log and save to a list.
    """
    logging.info("Processing whisper log : {}".format(whisper_log))
    instr_cnt = 0
    whisper_instr = ""

    with open(whisper_log, "r") as f, open(csv, "w") as csv_fd:
        trace_csv = RiscvInstructionTraceCsv(csv_fd)
        trace_csv.start_new_trace()
        for line in f:
            # Extract instruction infromation
            m = INSTR_RE.search(line)
            if m:
                logging.debug("-> mode: {}, pc:{}, bin:{}, instr:{}".format(
                  m.group('mode'), m.group('pc'), m.group('bin'),m.group('instr')))
                if re.search('ecall', m.group('instr')):
                    break
                if m.group('type') == 'r':
                    whisper_instr = m.group("instr").replace("\. +  ", "")
                    whisper_instr = whisper_instr.replace("\. - ", "-")
                    rv_instr_trace = RiscvInstructionTraceEntry()
                    rv_instr_trace.pc = m.group("pc")
                    rv_instr_trace.instr_str = whisper_instr
                    rv_instr_trace.binary = m.group("bin")
                    reg = "x" + str(int(m.group("reg"), 16))
                    rv_instr_trace.gpr.append(
                        gpr_to_abi(reg) + ":" + m.group("val"))
                    trace_csv.write_trace_entry(rv_instr_trace)
            instr_cnt += 1
    logging.info("Processed instruction count : {}".format(instr_cnt))
    logging.info("CSV saved to : {}".format(csv))


def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=str, help="Input whisper simulation log")
    parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
    parser.add_argument("-f", "--full_trace", dest="full_trace",
                        action="store_true",
                        help="Generate the full trace")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        help="Verbose logging")
    parser.set_defaults(full_trace=False)
    parser.set_defaults(verbose=False)
    args = parser.parse_args()
    setup_logging(args.verbose)
    # Process whisper log
    process_whisper_sim_log(args.log, args.csv, args.full_trace)


if __name__ == "__main__":
    main()
