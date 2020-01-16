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

Convert spike sim log to standard riscv instruction trace format
"""

import argparse
import os
import re
import sys
import logging

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *
from lib import *

RD_RE    = re.compile(r"(?P<pri>\d) 0x(?P<addr>[a-f0-9]+?) " \
                      "\((?P<bin>.*?)\) (?P<reg>[xf]\s*\d*?) 0x(?P<val>[a-f0-9]+)")
CORE_RE  = re.compile(r"core.*0x(?P<addr>[a-f0-9]+?) \(0x(?P<bin>.*?)\) (?P<instr>.*?)$")
INSTR_RE = re.compile(r"(?P<instr>[a-z\.0-9]+?)(\s+?)(?P<operand>.*)")
GPR_RE   = re.compile(r"^[a-z][0-9a-z]$")
ILLE_RE  = re.compile(r"trap_illegal_instruction")
PC_RE    = re.compile(r"pc+")
HEX_RE   = re.compile(r"^0x")

LOGGER = logging.getLogger()

def process_spike_sim_log(spike_log, csv, full_trace = 0):
  """Process SPIKE simulation log.

  Extract instruction and affected register information from spike simulation
  log and save to a list.
  """
  logging.info("Processing spike log : %s" % spike_log)
  instr_cnt = 0
  spike_instr = ""

  # Remove all the init spike boot instructions
  cmd = ("sed -i '/core.*0x0000000000001010/,$!d' %s" % spike_log)
  os.system(cmd)
  # Remove all instructions after ecall (end of program excecution)
  cmd = ("sed -i '/ecall/q' %s" % spike_log)
  os.system(cmd)

  gpr = {}
  gpr["zero"] = 0

  with open(spike_log, "r") as f, open(csv, "w") as csv_fd:
    trace_csv = RiscvInstructionTraceCsv(csv_fd)
    trace_csv.start_new_trace()
    for line in f:
      # Extract instruction infromation
      m = CORE_RE.search(line)
      if m:
        instr_cnt += 1
        spike_instr = m.group("instr").replace("pc + ", "")
        spike_instr = spike_instr.replace("pc - ", "-")
        rv_instr_trace = RiscvInstructionTraceEntry()
        rv_instr_trace.instr_str = spike_instr
        rv_instr_trace.addr = m.group("addr")
        rv_instr_trace.binary = m.group("bin")
        if spike_instr == "wfi":
          trace_csv.write_trace_entry(rv_instr_trace)
          continue
        nextline = f.readline()
        if nextline != "":
          if ILLE_RE.search(nextline):
            if full_trace:
              logging.debug("Illegal instruction: %s, opcode:%s" %
                            (rv_instr_trace.instr_str, rv_instr_trace.binary))
              trace_csv.write_trace_entry(rv_instr_trace)
            continue
          m = RD_RE.search(nextline)
          if m:
            # Extract RD information
            rv_instr_trace.rd = gpr_to_abi(m.group("reg").replace(" ",""))
            rv_instr_trace.rd_val = m.group("val")
            rv_instr_trace.privileged_mode = m.group("pri")
            gpr[rv_instr_trace.rd] = rv_instr_trace.rd_val
          else:
            # If full trace is not enabled, skip the entry that doesn't have
            # architectural state update.
            if not full_trace:
              continue
          if full_trace:
            s = INSTR_RE.search(spike_instr)
            if s:
              rv_instr_trace.instr = s.group("instr")
              operand_str = s.group("operand").replace(" ", "")
              operands = operand_str.split(",")
              assign_operand(rv_instr_trace, operands, gpr)
            else:
              rv_instr_trace.instr = spike_instr
        else:
          rv_instr_trace.instr = spike_instr
        trace_csv.write_trace_entry(rv_instr_trace)
  logging.info("Processed instruction count : %d" % instr_cnt)
  logging.info("CSV saved to : %s" % csv)


def main():
  # Parse input arguments
  parser = argparse.ArgumentParser()
  parser.add_argument("--log", type=str, help="Input spike simulation log")
  parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
  parser.add_argument("-f", "--full_trace", dest="full_trace", action="store_true",
                                         help="Generate the full trace")
  parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                                         help="Verbose logging")
  parser.set_defaults(full_trace=False)
  parser.set_defaults(verbose=False)
  args = parser.parse_args()
  setup_logging(args.verbose)
  # Process spike log
  process_spike_sim_log(args.log, args.csv, args.full_trace)


if __name__ == "__main__":
  main()
