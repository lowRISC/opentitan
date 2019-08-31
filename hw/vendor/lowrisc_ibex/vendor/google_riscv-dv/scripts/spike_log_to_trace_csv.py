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

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *

def process_spike_sim_log(spike_log, csv):
  """Process SPIKE simulation log.

  Extract instruction and affected register information from spike simulation
  log and save to a list.
  """
  print("Processing spike log : %s" % spike_log)
  instr_cnt = 0
  spike_instr = ""

  # Remove all the init spike boot instructions
  cmd = ("sed -i '/core.*0x0000000000001010/,$!d' %s" % spike_log)
  os.system(cmd)
  # Remove all instructions after ecall (end of program excecution)
  cmd = ("sed -i '/ecall/q' %s" % spike_log)
  os.system(cmd)

  with open(spike_log, "r") as f, open(csv, "w") as csv_fd:
    trace_csv = RiscvInstructiontTraceCsv(csv_fd)
    trace_csv.start_new_trace()
    for line in f:
      # Extract instruction infromation
      m = re.search(r"core(.*)\) (.*)", line)
      if m:
        spike_instr = m.group(2)
      else:
        # Extract register value information
        m = re.search(r"(?P<pri>\d) 0x(?P<addr>[a-f0-9]+?) " \
                       "\((?P<bin>.*?)\) x\s*(?P<reg>\d*?) 0x(?P<val>.*)", line)
        if m:
          # Write the extracted instruction to a csvcol buffer file
          instr_cnt += 1
          rv_instr_trace = RiscvInstructiontTraceEntry()
          rv_instr_trace.rd = gpr_to_abi("x%0s" % m.group("reg"))
          rv_instr_trace.rd_val = m.group("val")
          rv_instr_trace.privileged_mode = m.group("pri")
          rv_instr_trace.addr = m.group("addr")
          rv_instr_trace.binary = m.group("bin")
          rv_instr_trace.instr_str = spike_instr
          trace_csv.write_trace_entry(rv_instr_trace)
  print("Processed instruction count : %d" % instr_cnt)


def main():
  instr_trace = []
  # Parse input arguments
  parser = argparse.ArgumentParser()
  parser.add_argument("--log", type=str, help="Input spike simulation log")
  parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
  args = parser.parse_args()
  # Process spike log
  process_spike_sim_log(args.log, args.csv)

if __name__ == "__main__":
  main()
