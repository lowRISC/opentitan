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
    self.vd = ""
    self.vd_val = ""
    self.vs1 = ""
    self.vs1_val = ""
    self.vs2 = ""
    self.vs2_val = ""
    self.vs3 = ""
    self.vs3_val = ""
    self.rs3 = ""
    self.rs3_val = ""
    self.vtype_vsew = ""
    self.vtype_vmul = ""
    self.vtype_vediv = ""
    self.vm = ""
    self.updated_csr = ""
    self.updated_gpr = ""
    self.fd = ""
    self.fd_val = ""
    self.fs1 = ""
    self.fs1_val = ""
    self.fs2 = ""
    self.fs2_val = ""

  def get_trace_string(self):
    """Return a short string of the trace entry"""
    return ("%s -> %s(0x%s) addr:0x%s" %
           (self.instr_str, self.rd, self.rd_val, self.addr))

class RiscvInstructionTraceCsv(object):
  """RISC-V instruction trace CSV class

  This class provides functions to read/write trace CSV
  """

  def __init__(self, csv_fd):
    self.csv_fd = csv_fd
    self.gpr = {}


  def start_new_trace(self):
    """Create a CSV file handle for a new trace"""
    fields = [
        "instr", "rd", "rd_val", "rs1", "rs1_val", "rs2", "rs2_val",
        "rs3", "rs3_val", "imm", "str", "addr", "binary", "csr", "mode",
        "vd", "vd_val", "vs1", "vs1_val","vs2", "vs2_val","vs3", "vs3_val",
        "vtype_vsew", "vtype_vmul", "vtype_vediv", "vm", "updated_csr", "updated_gpr",
        "fd", "fd_val", "fs1", "fs1_val","fs2", "fs2_val"]
    self.csv_writer = csv.DictWriter(self.csv_fd, fieldnames=fields)
    self.csv_writer.writeheader()


  def read_trace(self, trace):
    """Read instruction trace from CSV file"""
    csv_reader = csv.DictReader(self.csv_fd)
    for row in csv_reader:
      new_trace = RiscvInstructionTraceEntry()
      new_trace.rd = row['rd']
      new_trace.rd_val = row['rd_val']
      new_trace.addr = row['addr']
      new_trace.binary = row['binary']
      new_trace.instr_str = row['str']
      trace.append(new_trace)


  def write_trace_entry(self, entry):
    """Write a new trace entry to CSV"""
    self.gpr[entry.rd] = entry.rd_val
    self.csv_writer.writerow({'str'           : entry.instr_str,
                              'rd'            : entry.rd,
                              'rd_val'        : entry.rd_val,
                              'rs1'           : entry.rs1,
                              'rs1_val'       : entry.rs1_val,
                              'rs2'           : entry.rs2,
                              'rs2_val'       : entry.rs2_val,
                              'rs3'           : entry.rs3,
                              'rs3_val'       : entry.rs3_val,
                              'addr'          : entry.addr,
                              'instr'         : entry.instr,
                              'imm'           : entry.imm,
                              'csr'           : entry.csr,
                              'binary'        : entry.binary,
                              'mode'          : entry.privileged_mode,
                              'vd'            : entry.vd,
                              'vd_val'        : entry.vd_val,
                              'vs1'           : entry.vs1,
                              'vs1_val'       : entry.vs1_val,
                              'vs2'           : entry.vs2,
                              'vs2_val'       : entry.vs2_val,
                              'vs3'           : entry.vs3,
                              'vs3_val'       : entry.vs3_val,
                              'vtype_vsew'    : entry.vtype_vsew,
                              'vtype_vmul'    : entry.vtype_vmul,
                              'vtype_vediv'   : entry.vtype_vediv,
                              'vm'            : entry.vm,
                              'updated_csr'   : entry.updated_csr,
                              'updated_gpr'   : entry.updated_gpr,
                              'fd'            : entry.fd,
                              'fd_val'        : entry.fd_val,
                              'fs1'           : entry.fs1,
                              'fs1_val'       : entry.fs1_val,
                              'fs2'           : entry.fs2,
                              'fs2_val'       : entry.fs2_val,
                })


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

ADDR_RE  = re.compile(r"(?P<imm>[\-0-9]+?)\((?P<rs1>.*)\)")

def assign_operand(trace, operands, gpr, stop_on_first_error = 0):
  """Assign the operand value of the instruction trace"""
  if trace.instr in ['lb', 'lh', 'lw', 'lbu', 'lhu', 'ld', 'lq', 'lwu', 'ldu',
                     'c.lw', 'c.ld', 'c.lq', 'c.lwsp', 'c.ldsp', 'c.lqsp']:
    # TODO: Support regular load/store format
    m = ADDR_RE.search(operands[1])
    # Load instruction
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    if m:
      trace.imm = get_imm_hex_val(m.group('imm'))
      trace.rs1 = m.group('rs1')
      trace.rs1_val = gpr[trace.rs1]
    else:
      logging.info("Unexpected load address %0s", operands[1])
  elif trace.instr in ['sb', 'sh', 'sw', 'sd', 'sq', 'c.sw', 'c.sd', 'c.sq',
                       'c.swsp', 'c.sdsp', 'c.sqsp']:
    # Store instruction
    m = ADDR_RE.search(operands[1])
    # Load instruction
    trace.rs2 = operands[0]
    trace.rs2_val = gpr[trace.rs2]
    if m:
      trace.imm = get_imm_hex_val(m.group('imm'))
      trace.rs1 = m.group('rs1')
      trace.rs1_val = gpr[trace.rs1]
    else:
      logging.info("Unexpected store address %0s", operands[1])
  elif trace.instr in [
        'mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu',
        'mulw', 'muld', 'divw', 'divuw', 'divd', 'remw', 'remd', 'remuw',
        'remud', 'sll', 'srl', 'sra', 'add', 'sub', 'xor', 'or', 'and',
        'slt', 'sltu', 'sllw', 'slld', 'srlw', 'srld', 'sraw', 'srad',
        'addw', 'addd', 'subw', 'subd']:
    # R type instruction
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = operands[2]
    trace.rs2_val = gpr[trace.rs2]
  elif trace.instr in [
        'c.add', 'c.addw', 'c.mv', 'c.sub', 'c.and', 'c.or', 'c.xor', 'c.subw']:
    # CR type
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = operands[1]
    trace.rs2_val = gpr[trace.rs2]
  elif trace.instr in ['c.jr']:
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = 'zero'
    trace.rs2_val = '0'
    trace.rd = 'zero'
    trace.rd_val = '0'
  elif trace.instr in ['c.jr', 'c.jalr']:
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = 'zero'
    trace.rs2_val = '0'
  elif trace.instr in [
        'slli', 'srli', 'srai', 'addi', 'xori', 'ori', 'andi', 'slti',
        'sltiu', 'slliw', 'sllid', 'srliw', 'srlid', 'sraiw', 'sraid',
         'addiw', 'addid']:
    # I type instruction
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val(operands[2])
  elif trace.instr in ['c.addi16sp', 'c.addi4spn']:
    trace.rs1 = 'sp'
    trace.rs1_val = gpr[trace.rs1]
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.imm = get_imm_hex_val(operands[-1])
  elif trace.instr in ['c.addi', 'c.addiw', 'c.li', 'c.lui',
                       'c.slli', 'c.srai', 'c.srli', 'c.andi']:
    # CI/CIW type
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val(operands[-1])
  elif trace.instr in ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu']:
    # SB type instruction
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = operands[1]
    trace.rs2_val = gpr[trace.rs2]
    trace.imm = get_imm_hex_val(operands[2])
  elif trace.instr in ['c.beqz', 'c.bnez']:
    # CB type instruction
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val(operands[1])
  elif trace.instr in ['csrrw', 'csrrs', 'csrrc']:
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.csr = operands[1]
    trace.rs1 = operands[2]
    trace.rs1_val = gpr[trace.rs1]
  elif trace.instr in ['csrrwi', 'csrrsi', 'csrrci']:
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.csr = operands[1]
    trace.imm = get_imm_hex_val(operands[2])
  elif trace.instr in [
        'scall', 'sbreak', 'fence', 'fence.i', 'ecall', 'ebreak', 'wfi',
        'sfence.vma', 'c.ebreak', 'nop', 'c.nop']:
    trace.rd  = 'zero'
    trace.rs1 = 'zero'
    trace.rs2 = 'zero'
    trace.rd_val  = '0'
    trace.rs1_val = '0'
    trace.rs2_val = '0'
    trace.imm = get_imm_hex_val('0')
  elif trace.instr in ['lui', 'auipc']:
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.imm = get_imm_hex_val(operands[1])
  elif trace.instr in ['jal']:
    if len(operands) == 1:
      trace.imm = get_imm_hex_val(operands[0])
    else:
      trace.imm = get_imm_hex_val(operands[1])
  elif trace.instr in ['jalr']:
    if len(operands) == 1:
      trace.rs1 = operands[0]
      trace.rs1_val = gpr[trace.rs1]
      trace.imm = get_imm_hex_val('0')
    else:
      trace.rs1 = operands[1]
      trace.rs1_val = gpr[trace.rs1]
      trace.imm = get_imm_hex_val(operands[2])
  elif trace.instr in ['c.j']:
    trace.imm = get_imm_hex_val(operands[0])
  elif trace.instr in ['c.jal']:
    if len(operands) == 1:
      trace.imm = get_imm_hex_val(operands[0])
    else:
      trace.imm = get_imm_hex_val(operands[1])
  # Pseudo instruction convertion below
  elif trace.instr in ['mv']:
    trace.instr = 'addi'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val('0')
  elif trace.instr in ['not']:
    trace.instr = 'xori'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val('-1')
  elif trace.instr in ['neg']:
    trace.instr = 'sub'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = 'zero'
    trace.rs1_val = '0'
    trace.rs2 = operands[1]
    trace.rs2_val = gpr[trace.rs2]
  elif trace.instr in ['negw']:
    trace.instr = 'subw'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = 'zero'
    trace.rs1_val = '0'
    trace.rs2 = operands[1]
    trace.rs2_val = gpr[trace.rs2]
  elif trace.instr in ['sext.w']:
    trace.instr = 'addiw'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val('0')
  elif trace.instr in ['seqz']:
    trace.instr = 'sltiu'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val('1')
  elif trace.instr in ['snez']:
    trace.instr = 'sltu'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = 'zero'
    trace.rs1_val = '0'
    trace.rs2 = operands[1]
    trace.rs2_val = gpr[trace.rs2]
  elif trace.instr in ['sltz']:
    trace.instr = 'slt'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = 'zero'
    trace.rs2_val = '0'
  elif trace.instr in ['sgtz']:
    trace.instr = 'slt'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = 'zero'
    trace.rs1_val = '0'
    trace.rs2 = operands[1]
    trace.rs2_val = gpr[trace.rs2]
  elif trace.instr in ['beqz', 'bnez', 'bgez', 'bltz']:
    trace.instr = trace.instr[0:3]
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = 'zero'
    trace.rs2_val = '0'
    trace.imm = get_imm_hex_val(operands[1])
  elif trace.instr in ['blez']:
    trace.instr = 'bge'
    trace.rs1 = 'zero'
    trace.rs1_val = '0'
    trace.rs2 = operands[0]
    trace.rs2_val = gpr[trace.rs2]
    trace.imm = get_imm_hex_val(operands[1])
  elif trace.instr in ['bgtz']:
    trace.instr = 'blt'
    trace.rs1 = 'zero'
    trace.rs1_val = '0'
    trace.rs2 = operands[0]
    trace.rs2_val = gpr[trace.rs2]
    trace.imm = get_imm_hex_val(operands[1])
  elif trace.instr in ['csrr']:
    trace.instr = 'csrrw'
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.csr = operands[1]
    trace.rs1 = 'zero'
    trace.rs1_val = '0'
  elif trace.instr in ['csrw', 'csrs', 'csrc']:
    trace.instr = 'csrr' + trace.instr[-1]
    trace.csr = operands[0]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.rd = 'zero'
    trace.rd_val = '0'
  elif trace.instr in ['csrwi', 'csrsi', 'csrci']:
    trace.instr = 'csrr' + trace.instr[-2:]
    trace.rd = 'zero'
    trace.rd_val = '0'
    trace.csr = operands[0]
    trace.imm = get_imm_hex_val(operands[1])
  elif trace.instr in ['j']:
    trace.instr = 'jal'
    trace.rd = 'zero'
    trace.rd_val = '0'
    trace.imm = get_imm_hex_val(operands[0])
  elif trace.instr in ['jr']:
    trace.instr = 'jal'
    trace.rd = 'zero'
    trace.rd_val = '0'
    trace.rs1 = operands[0]
    if trace.rs1 in gpr:
      trace.rs1_val = gpr[trace.rs1]
  elif trace.instr in ['li']:
    trace.instr = 'li'
  elif trace.instr[0:2] in ['lr', 'am', 'sc']:
    # TODO: Support A-extension
    pass
  else:
    # TODO: Support other instructions
    logging.debug("Unsupported instr : %s (%s)" %
                  (trace.instr, trace.instr_str))
    if stop_on_first_error:
        sys.exit(RET_FATAL)
