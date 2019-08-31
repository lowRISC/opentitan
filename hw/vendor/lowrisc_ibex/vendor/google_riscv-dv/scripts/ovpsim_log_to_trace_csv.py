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

Convert ovpsim sim log to standard riscv instruction trace format
"""
import re
import os
import argparse

from riscv_trace_csv import *

def process_ovpsim_sim_log(ovpsim_log, csv):
  """Process SPIKE simulation log.

  Extract instruction and affected register information from ovpsim simulation
  log and save to a list.
  """
  print("Processing ovpsim log : %s" % ovpsim_log)
  instr_cnt = 0
  trace_instr = ""
  trace_bin = ""
  trace_addr = ""

  # Remove the header part of ovpsim log
  cmd = ("sed -i '/Info 1:/,$!d' %s" % ovpsim_log)
  os.system(cmd)
  # Remove all instructions after ecall (end of program excecution)
  cmd = ("sed -i '/ecall/q' %s" % ovpsim_log)
  os.system(cmd)

  with open(ovpsim_log, "r") as f, open(csv, "w") as csv_fd:
    trace_csv = RiscvInstructiontTraceCsv(csv_fd)
    trace_csv.start_new_trace()
    for line in f:
      # Extract instruction infromation
      m = re.search(r"riscvOVPsim.*, 0x(?P<addr>.*?)(?P<section>\(.*\): ?)" \
                     "(?P<bin>[a-f0-9]*?)\s+(?P<instr>.*?)$", line)
      if m:
        trace_bin = m.group("bin")
        trace_instr = m.group("instr")
        trace_addr = m.group("addr")
        instr_cnt += 1
      else:
        # Extract register value information
        n = re.search(r" (?P<rd>[a-z0-9]{2,3}?) (?P<pre>[a-f0-9]+?)" \
                       " -> (?P<val>[a-f0-9]+?)$", line)
        if n:
          # Write the extracted instruction to a csvcol buffer file
          # print("%0s %0s = %0s" % (trace_instr, m.group("rd"), m.group("val")))
          rv_instr_trace = RiscvInstructiontTraceEntry()
          rv_instr_trace.rd = n.group("rd")
          rv_instr_trace.rd_val = n.group("val")
          rv_instr_trace.instr_str = trace_instr
          rv_instr_trace.binary = trace_bin
          rv_instr_trace.addr = trace_addr
          trace_csv.write_trace_entry(rv_instr_trace)
  print("Processed instruction count : %d" % instr_cnt)


def main():
  instr_trace = []
  # Parse input arguments
  parser = argparse.ArgumentParser()
  parser.add_argument("--log", type=str, help="Input ovpsim simulation log")
  parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
  args = parser.parse_args()
  # Process ovpsim log
  process_ovpsim_sim_log(args.log, args.csv)


if __name__ == "__main__":
  main()

