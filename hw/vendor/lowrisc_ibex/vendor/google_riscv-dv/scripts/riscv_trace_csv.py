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
    self.instr = ""
    self.privileged_mode = ""
    self.csr = ""

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
    self.gpr = {}


  def start_new_trace(self):
    """Create a CSV file handle for a new trace"""
    fields = ["instr", "rd", "rd_val", "rs1", "rs1_val", "rs2", "rs2_val",
              "imm", "str", "addr", "binary", "csr", "mode"]
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
    self.gpr[entry.rd] = entry.rd_val
    self.csv_writer.writerow({'str'     : entry.instr_str,
                              'rd'      : entry.rd,
                              'rd_val'  : entry.rd_val,
                              'rs1'     : entry.rs1,
                              'rs1_val' : entry.rs1_val,
                              'rs2'     : entry.rs2,
                              'rs2_val' : entry.rs2_val,
                              'addr'    : entry.addr,
                              'instr'   : entry.instr,
                              'imm'     : entry.imm,
                              'csr'     : entry.csr,
                              'binary'  : entry.binary})


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
    "x31" : "t6",
    "f0"  : "ft0",
    "f1"  : "ft1",
    "f2"  : "ft2",
    "f3"  : "ft3",
    "f4"  : "ft4",
    "f5"  : "ft5",
    "f6"  : "ft6",
    "f7"  : "ft7",
    "f8"  : "fs0",
    "f9"  : "fs1",
    "f10" : "fa0",
    "f11" : "fa1",
    "f12" : "fa2",
    "f13" : "fa3",
    "f14" : "fa4",
    "f15" : "fa5",
    "f16" : "fa6",
    "f17" : "fa7",
    "f18" : "fs2",
    "f19" : "fs3",
    "f20" : "fs4",
    "f21" : "fs5",
    "f22" : "fs6",
    "f23" : "fs7",
    "f24" : "fs8",
    "f25" : "fs9",
    "f26" : "fs10",
    "f27" : "fs11",
    "f28" : "ft8",
    "f29" : "ft9",
    "f30" : "ft10",
    "f31" : "ft11",
  }
  return switcher.get(gpr, "na")
