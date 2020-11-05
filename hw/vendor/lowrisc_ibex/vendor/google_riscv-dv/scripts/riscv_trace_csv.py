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
import re
import logging
import sys
from lib import *


class RiscvInstructionTraceEntry(object):
    """RISC-V instruction trace entry"""

    def __init__(self):
        self.gpr = []
        self.csr = []
        self.instr = ""
        self.operand = ""
        self.pc = ""
        self.binary = ""
        self.instr_str = ""
        self.mode = ""

    def get_trace_string(self):
        """Return a short string of the trace entry"""
        return ("pc[{}] {}: {} {}".format(
            self.pc, self.instr_str, " ".join(self.gpr), " ".join(self.csr)))


class RiscvInstructionTraceCsv(object):
    """RISC-V instruction trace CSV class

    This class provides functions to read/write trace CSV
    """

    def __init__(self, csv_fd):
        self.csv_fd = csv_fd

    def start_new_trace(self):
        """Create a CSV file handle for a new trace"""
        fields = ["pc", "instr", "gpr", "csr", "binary", "mode", "instr_str",
                  "operand", "pad"]
        self.csv_writer = csv.DictWriter(self.csv_fd, fieldnames=fields)
        self.csv_writer.writeheader()

    def read_trace(self, trace):
        """Read instruction trace from CSV file"""
        csv_reader = csv.DictReader(self.csv_fd)
        for row in csv_reader:
            new_trace = RiscvInstructionTraceEntry()
            new_trace.gpr = row['gpr'].split(';')
            new_trace.csr = row['csr'].split(';')
            new_trace.pc = row['pc']
            new_trace.operand = row['operand']
            new_trace.binary = row['binary']
            new_trace.instr_str = row['instr_str']
            new_trace.instr = row['instr']
            new_trace.mode = row['mode']
            trace.append(new_trace)

    # TODO: Convert pseudo instruction to regular instruction

    def write_trace_entry(self, entry):
        """Write a new trace entry to CSV"""
        self.csv_writer.writerow({'instr_str': entry.instr_str,
                                  'gpr'      : ";".join(entry.gpr),
                                  'csr'      : ";".join(entry.csr),
                                  'operand'  : entry.operand,
                                  'pc'       : entry.pc,
                                  'binary'   : entry.binary,
                                  'instr'    : entry.instr,
                                  'mode'     : entry.mode})


def get_imm_hex_val(imm):
    """Get the hex representation of the imm value"""
    if imm[0] == '-':
        is_negative = 1
        imm = imm[1:]
    else:
        is_negative = 0
    imm_val = int(imm, 0)
    if is_negative:
        imm_val = -imm_val
    hexstr = sint_to_hex(imm_val)
    return hexstr[2:]
