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
                      "\((?P<bin>.*?)\) x\s*(?P<reg>\d*?) 0x(?P<val>[a-f0-9]+)")
CORE_RE  = re.compile(r"core.*0x(?P<addr>[a-f0-9]+?) \(0x(?P<bin>.*?)\) (?P<instr>.*?)$")
INSTR_RE = re.compile(r"(?P<instr>[a-z\.0-9]+?)(\s+?)(?P<operand>.*)")
GPR_RE   = re.compile(r"^[a-z][0-9a-z]$")
ILLE_RE  = re.compile(r"trap_illegal_instruction")
ADDR_RE  = re.compile(r"(?P<imm>[\-0-9]+?)\((?P<rs1>.*)\)")
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
    trace_csv = RiscvInstructiontTraceCsv(csv_fd)
    trace_csv.start_new_trace()
    for line in f:
      # Extract instruction infromation
      m = CORE_RE.search(line)
      if m:
        spike_instr = m.group("instr").replace("pc + ", "")
        spike_instr = spike_instr.replace("pc - ", "-")
        rv_instr_trace = RiscvInstructiontTraceEntry()
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
              trace_csv.write_trace_entry(rv_instr_trace)
            continue
          m = RD_RE.search(nextline)
          if m:
            # Extract RD information
            instr_cnt += 1
            rv_instr_trace.rd = gpr_to_abi("x%0s" % m.group("reg"))
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


def sint_to_hex(val):
  """Signed integer to hex conversion"""
  return str(hex((val + (1 << 32)) % (1 << 32)))


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


def assign_operand(trace, operands, gpr):
  #logging.debug("-> [%0s] %0s" % (trace.instr, trace.instr_str))
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
  elif trace.instr in ['mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu',
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
  elif trace.instr in ['c.add', 'c.addw', 'c.mv', 'c.sub', 'c.jr', 'c.and', 'c.or',
                       'c.xor', 'c.subw']:
    # CR type
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[0]
    trace.rs1_val = gpr[trace.rs1]
    trace.rs2 = operands[1]
    trace.rs2_val = gpr[trace.rs2]
  elif trace.instr in ['slli', 'srli', 'srai', 'addi', 'xori', 'ori', 'andi', 'slti',
                       'sltiu', 'slliw', 'sllid', 'srliw', 'srlid', 'sraiw', 'sraid',
                       'addiw', 'addid']:
    # I type instruction
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
    trace.imm = get_imm_hex_val(operands[2])
  elif trace.instr in ['c.addi', 'c.addiw', 'c.addi16sp', 'c.addi4spn', 'c.li', 'c.lui',
                       'c.slli', 'c.srai', 'c.srli', 'c.andi']:
    # CI/CIW type
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
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
  elif trace.instr in ['scall', 'sbreak', 'fence', 'fence.i', 'ecall', 'ebreak', 'wfi',
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
  elif trace.instr in ['c.j', 'c.jal']:
    trace.imm = get_imm_hex_val(operands[0])
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
    trace.rs1 = operands[1]
    trace.rs1_val = gpr[trace.rs1]
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
    logging.info("Unsupported instr : %s" % trace.instr)

def main():
  instr_trace = []
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
