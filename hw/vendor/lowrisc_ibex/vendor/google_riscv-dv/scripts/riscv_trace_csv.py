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

Class for RISC-V instruction trace CSV
"""

import csv

class RiscvInstructiontTraceEntry(object):
  """RISC-V instruction trace entry"""
  def __init__(self):
    self.rd = ""
    self.rd_val = ""
    self.rs1 = ""
    self.rs1_val = ""
    self.rs2 = ""
    self.rs2_val = ""
    self.imm = ""
    self.instr_name = ""
    self.addr = ""
    self.binary = ""
    self.instr_str = ""
    self.privileged_mode = ""

  def get_trace_string(self):
    """Return a short string of the trace entry"""
    return ("%s -> %s(0x%s) addr:0x%s" %
           (self.instr_str, self.rd, self.rd_val, self.addr))

class RiscvInstructiontTraceCsv(object):
  """RISC-V instruction trace CSV class

  This class provides functions to read/write trace CSV
  """

  def __init__(self, csv_fd):
    self.csv_fd = csv_fd


  def start_new_trace(self):
    """Create a CSV file handle for a new trace"""
    fields = ["instr", "rd", "rd_val", "rs1", "rs1_val", "rs2", "rs2_val",
              "imm", "str", "addr", "binary", "mode"]
    self.csv_writer = csv.DictWriter(self.csv_fd, fieldnames=fields)
    self.csv_writer.writeheader()


  def read_trace(self, trace):
    """Read instruction trace from CSV file"""
    csv_reader = csv.DictReader(self.csv_fd)
    for row in csv_reader:
      new_trace = RiscvInstructiontTraceEntry()
      new_trace.rd = row['rd']
      new_trace.rd_val = row['rd_val']
      new_trace.addr = row['addr']
      new_trace.binary = row['binary']
      new_trace.instr_str = row['str']
      trace.append(new_trace)


  def write_trace_entry(self, entry):
    """Write a new trace entry to CSV"""
    self.csv_writer.writerow({'str'    : entry.instr_str,
                              'rd'     : entry.rd,
                              'rd_val' : entry.rd_val,
                              'binary' : entry.binary,
                              'addr'   : entry.addr})


def gpr_to_abi(gpr):
  """Convert a general purpose register to its corresponding abi name"""
  switcher = {
    "x0"  : "zero",
    "x1"  : "ra",
    "x2"  : "sp",
    "x3"  : "gp",
    "x4"  : "tp",
    "x5"  : "t0",
    "x6"  : "t1",
    "x7"  : "t2",
    "x8"  : "s0",
    "x9"  : "s1",
    "x10" : "a0",
    "x11" : "a1",
    "x12" : "a2",
    "x13" : "a3",
    "x14" : "a4",
    "x15" : "a5",
    "x16" : "a6",
    "x17" : "a7",
    "x18" : "s2",
    "x19" : "s3",
    "x20" : "s4",
    "x21" : "s5",
    "x22" : "s6",
    "x23" : "s7",
    "x24" : "s8",
    "x25" : "s9",
    "x26" : "s10",
    "x27" : "s11",
    "x28" : "t3",
    "x29" : "t4",
    "x30" : "t5",
    "x31" : "t6"
  }
  return switcher.get(gpr, "na")
