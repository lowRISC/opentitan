"""
Copyright 2019 Google LLC
Copyright 2019 Imperas Software Ltd

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Convert ovpsim sim log to standard riscv-dv .csv instruction trace format
"""
import re
import os
import argparse
import logging

import sys
from lib import *

from riscv_trace_csv import *

try:
  from ovpsim_log_to_trace_csv_vectors import *
except:
  def assign_operand_vector(a,b,c,d):
    """ stub version when no vector processing included """
    logging.info("No OVPsim vector instruction processing included")
    if stop_on_first_error:
      sys.exit(RET_FATAL)
  def is_an_extension_instruction(instr):
    if instr and 'v' in instr[0]:
      return True
    return False


stop_on_first_error = 0

def fatal (s):
  """ ensure we end if a problem """
  logging.fatal("ERROR: "+s)
  sys.exit(RET_FATAL)

def convert_mode(pri, line):
  """ OVPsim uses text string, convert to numeric """
  if "Machine"    in pri:    return str(3)
  if "Supervisor" in pri:    return str(1)
  if "User"       in pri:    return str(0)
  logging.error("convert_mode = UNKNOWN PRIV MODE  [%s]: %s" % (pri, line))
  if stop_on_first_error:
      sys.exit(RET_FATAL)

REGS = ["zero","ra","sp","gp","tp","t0","t1","t2","s0","s1",
        "a0","a1","a2","a3","a4","a5","a6","a7",
        "s2","s3","s4","s5","s6","s7","s8","s9","s10","s11",
        "t3","t4","t5","t6"]
FREGS = ["ft0","ft1","ft2","ft3","ft4","ft5","ft6","ft7","fs0","fs1","fa0",
         "fa1","fa2","fa3","fa4","fa5","fa6","fa7","fs2","fs3","fs4","fs5",
         "fs6","fs7","fs8","fs9","fs10","fs11","ft8","ft9","ft10","ft11"]

def process_jal(trace, operands, gpr):
  """ correctly process jal """
  # TODO need to merge with jalr
  ## jal rd, imm
  if len(operands) == 2:
    trace.rd = operands[0]
    trace.rd_val = gpr[trace.rd]
    trace.imm = get_imm_hex_val("0x" + operands[1])
  else:
    fatal("process_jal(%s) wrong num operands (%d)" %
      (trace.instr, len(operands)))

def process_jalr(trace, operands, gpr):
  """ process jalr """
  ## jalr x3
  ## jalr 9(x3)
  ## jalr x2,x3
  ## jalr x2,4(x3)
  if len(operands) == 1:
    m = ADDR_RE.search(operands[0])
    trace.rd = 'ra'
    trace.rd_val = gpr['ra']
    if m: # jalr 9(x3)
      trace.rs1 = m.group('rs1')
      trace.rs1_val = gpr[trace.rs1]
      trace.imm = get_imm_hex_val(m.group('imm'))
    else: # jalr x3
      trace.rs1 = operands[0]
      trace.rs1_val = gpr[trace.rs1]
      trace.imm = get_imm_hex_val('0')
  elif len(operands) == 2:
      trace.rd = operands[0]
      trace.rd_val = gpr[trace.rd]
      m = ADDR_RE.search(operands[1])
      if m: # jalr x2,4(x3)
        trace.rs1 = m.group('rs1')
        trace.rs1_val = gpr[trace.rs1]
        trace.imm = get_imm_hex_val(m.group('imm'))
      else: # jalr x2,x3
        trace.rs1 = operands[1]
        trace.rs1_val = gpr[trace.rs1]
        trace.imm = get_imm_hex_val('0')

def process_if_compressed(prev_trace):
  """ convert naming for compressed instructions """
  if len(prev_trace.binary) == 4: # compressed are always 4 hex digits
    prev_trace.instr = "c."+prev_trace.instr
    # logging.debug("process_if_compressed(%s, %s)" %
    #   (prev_trace.instr, prev_trace.binary))

pseudos={
    'mv'        :'addi',
    'not'       :'xori',
    'neg'       :'sub',
    'negw'      :'subw',
    'sext.w'    :'addiw',
    'seqz'      :'sltiu',
    'snez'      :'sltu',
    'sltz'      :'slt',
    'sgtz'      :'slt',
    'beqz'      :'beg',
    'bnez'      :'bnez',
    'bgez'      :'bgez',
    'bltz'      :'blt',
    'blez'      :'bge',
    'bgtz'      :'blt',
    'csrr'      :'csrrw',
    'csrw'      :'csrrw',
    'csrs'      :'csrrs',
    'csrc'      :'csrrc',
    'csrwi'     :'csrrwi',
    'csrsi'     :'csrrsi',
    'csrci'     :'csrrci',
    'j'         :'jal',
    'jr'        :'jal',
    }

def check_conversion(entry):
  """ after conversion check that the entry was converted correctly """
  instr_str_0 =entry.instr_str.split(" ")[0]
  instr       =entry.instr.split(" ")[0]
  if "c." in instr[0:2]:
    instr = instr[2:]
  if instr in instr_str_0:
    return # same
  #logging.debug("converted pseudo %10s -> %s" % (instr_str_0, instr))
  if instr_str_0 in pseudos:
    p_instr = pseudos[instr_str_0]
    if p_instr in instr:
      return # is pseudo, converted ok
    logging.error(
      "converted        %10s -> %s <<-- not correct pseudo (%s)" %
        (instr_str_0, instr, p_instr))
    if stop_on_first_error:
      sys.exit(RET_FATAL)
  logging.error("converted        %10s -> %s  <<-- not correct at all" %
      (instr_str_0, instr))
  if stop_on_first_error:
    sys.exit(RET_FATAL)

operands_list = ["rd","rs1","rs2","vd","vs1","vs2","vs3","fd","fs1","fs2"]

def update_operands_values(trace, gpr):
  """ ensure operands have been updated """
  for op in operands_list:
    exec("if trace.%0s in gpr: trace.%0s_val = gpr[trace.%0s]" % (op, op, op))

def show_line_instr(line, i):
  """ show line """
  if is_an_extension_instruction(i.instr):
    logging.debug("%s" % (line.strip()))
    logging.debug(
      "  -->> instr_str(%s) binary(%s) addr(%s) mode(%s) instr(%s)"
      % (     i.instr_str, i.binary,  i.addr, i.privileged_mode,i.instr))

def check_num_operands(instr_str, num_operands, n):
  """ ensure consistency """
  if n != num_operands:
    fatal("%s: num operands wrong, expected (%d) got (%d)" % (instr_str,
      n, num_operands))

def is_csr(r):
  """ see if r is a csr """
  # TODO add more as needed - could look in the enum privileged_reg_t  or the cores settings: implemented_csr[]
  if r in ["mtvec","pmpaddr0","pmpcfg0","mstatus","mepc","mscratch","mcause",
      "mtval","vl","vtype"]:
    return True
  else:
    return False

def process_branch_offset (opn, operands, prev_trace):
  """ convert from ovpsim logs branch offsets as absolute to relative """
  addr = operands[opn]
  pc = prev_trace.addr
  offset_dec = int(addr, 16) - int(pc, 16)
  offset = hex(offset_dec)
  operands[opn] = offset

def process_ovpsim_sim_log(ovpsim_log, csv, full_trace = 1, stop = 0,
  dont_truncate_after_first_ecall = 0,
  verbose2 = False):
  """Process OVPsim simulation log.

  Extract instruction and affected register information from ovpsim simulation
  log and save to a list.
  """

  stop_on_first_error = stop

  logging.info("Processing ovpsim log : %s" % ovpsim_log)

  logging.debug("Flags [%s %s %s]" %
    ("full_trace" if full_trace else "",
     "stop_on_first_error" if stop else "",
     "dont_truncate_after_first_ecall" if dont_truncate_after_first_ecall else ""))

  # Remove the header part of ovpsim log
  cmd = ("sed -i '/Info 1:/,$!d' %s" % ovpsim_log)
  os.system(cmd)
  # Remove all instructions after end of trace data (end of program excecution)
  if dont_truncate_after_first_ecall:
    cmd = ("sed -i '/^Info --/q' %s" % ovpsim_log)
    logging.info("Dont truncate logfile after first ecall: %s", ovpsim_log)
  else:
    cmd = ("sed -i '/ecall/q' %s" % ovpsim_log)
  os.system(cmd)

  # storage and initial values of gpr and csr

  gpr = {}
  csr = {}

  for g in REGS: # base isa gprs
    gpr[g] = 0
  for i in range(32): # add in v0-v31 gprs
    gpr["v"+str(i)] = 0
  for f in FREGS: # floating point gprs
    gpr[f] = 0

  csr["vl"]    = 0
  csr["vtype"] = 0

  instr_cnt = 0
  with open(ovpsim_log, "r") as f, open(csv, "w") as csv_fd:
    trace_csv = RiscvInstructionTraceCsv(csv_fd)
    trace_csv.start_new_trace()
    prev_trace = 0
    logit = 0
    for line in f:
      # Extract instruction infromation
      m = re.search(r"riscvOVPsim.*, 0x(?P<addr>.*?)(?P<section>\(.*\): ?)" \
                    "(?P<mode>[A-Za-z]*?)\s+(?P<bin>[a-f0-9]*?)\s+(?P<instr_str>.*?)$", line)
      if m:
        # its instruction disassembly line
        if prev_trace: # write out the previous one when find next one
          check_conversion(prev_trace)
          update_operands_values(prev_trace, gpr)
          instr_cnt += 1
          trace_csv.write_trace_entry(prev_trace)
          if verbose2:
            logging.debug("prev_trace:: "+str(prev_trace.__dict__))
            logging.debug("csr       :: "+str(csr))
            logging.debug("gpr       :: "+str(gpr))
          if logit:
            # fatal ("stop for now")
            pass
          prev_trace = 0
        prev_trace = RiscvInstructionTraceEntry()
        prev_trace.instr_str = m.group("instr_str")
        prev_trace.instr = prev_trace.instr_str.split(" ")[0]
        prev_trace.binary = m.group("bin")
        prev_trace.addr = m.group("addr")
        prev_trace.section = m.group("section")
        prev_trace.privileged_mode = convert_mode(m.group("mode"), line)
        prev_trace.updated_csr = []
        prev_trace.updated_gpr = []
        #if prev_trace.instr in ["vsetvli"]:
        #if prev_trace.instr in ["vlh.v"]:
        #if prev_trace.instr in ["vmul.vx"]:
        if prev_trace.instr in ["vsetvl"]:
          logit = 1
          verbose2 = True

        show_line_instr(line, prev_trace)

        if full_trace:
          # TODO - when got full ins decode remove this
          if "fsw" in line or \
            "fnmsub.d" in line or \
            "fsd" in line:
            # "fsriw" in line or \
            # "flw" in line or \
            logging.debug ("Ignoring ins...(%s) " % (line))
            continue
          process_if_compressed(prev_trace)
          o = re.search (r"(?P<instr>[a-z]*?)\s(?P<operand>.*)",
                         prev_trace.instr_str)
          if o:
            operand_str = o.group("operand").replace(" ", "")
            operands = operand_str.split(",")
            if (prev_trace.instr in ['jalr', 'c.jalr']):
              process_jalr(prev_trace, operands, gpr)
            elif (prev_trace.instr in ['jal','c.jal']):
              process_jal(prev_trace, operands, gpr)
            else:
              if is_an_extension_instruction(prev_trace.instr):
                assign_operand_vector(prev_trace, operands, gpr, stop_on_first_error)
              elif 'f' in prev_trace.instr[0] or "c.f" in prev_trace.instr[0:3]:
                pass # ignore floating point. TODO include them
              else:
                if prev_trace.instr in ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu']:
                  process_branch_offset (2, operands, prev_trace)
                elif prev_trace.instr in [
                  'c.beqz', 'c.bnez', 'beqz', 'bnez', 'bgez', 'bltz', 'blez', 'bgtz']:
                  process_branch_offset (1, operands, prev_trace)
                if prev_trace.instr in ['j', 'c.j']:
                  operands[0] = "0x" + operands[0] # ovpsim has no '0x' so need to add it.
                assign_operand(prev_trace, operands, gpr, stop_on_first_error)
          else:
            # logging.debug("no operand for [%s] in [%s]" % (trace_instr,
            #   trace_instr_str))
            pass
      else:
        # its a csr, gpr new value or report
        if verbose2:
          logging.debug ("reg change... [%s]" % (line.strip()))
        # Extract register change value information
        c = re.search(r" (?P<r>[a-z]*[0-9]{0,2}?) (?P<pre>[a-f0-9]+?)" \
                       " -> (?P<val>[a-f0-9]+?)$", line)
        if c and is_csr (c.group("r")):
          csr[c.group("r")] = c.group("val")
          if verbose2:
            logging.debug("c:csr %0s = %0s" % (c.group("r"), c.group("val")))
          csr[c.group("r")] = c.group("val")
          # prev_trace.updated_csr.append(c.group("r"))
          prev_trace.updated_csr.append([c.group("r"), c.group("val")])
          continue
        n = re.search(r" (?P<r>[a-z]{1,3}[0-9]{0,2}?) (?P<pre>[a-f0-9]+?)" \
                       " -> (?P<val>[a-f0-9]+?)$", line)
        if n: # gpr
          if verbose2:
            logging.debug(("n:gpr %0s = %0s" % (n.group("r"), n.group("val"))))
          if not (n.group("r") in ["frm", "mie"]):
            prev_trace.updated_gpr.append([n.group("r"), n.group("val")])
            if is_an_extension_instruction(prev_trace.instr):
              gpr[n.group("r")] = n.group("val")
            else:
              # backwards compatible
              prev_trace.rd = n.group("r")
              prev_trace.rd_val  = n.group("val")
              gpr[prev_trace.rd] = prev_trace.rd_val
            if 0:
              print("write entry [[%d]]: rd[%s] val[%s] instr(%s) bin(%s) addr(%s)"
                    % (instr_cnt, rv_instr_trace.rd, rv_instr_trace.rd_val,
                       trace_instr_str, prev_trace.binary, prev_trace.addr))
              print (rv_instr_trace.__dict__)
              sys.exit(RET_FATAL)
        else:
          line = line.strip()
          if verbose2: logging.debug("ignoring line: [%s] %s " %
              (str(instr_cnt), line))
          line = re.sub(' +', ' ', line)
          split = line.split(" ")
          if len(split) == 1: continue
          item = split[1]
          if "----" in item: continue
          if "REPORT" in line or item in [ # TODO sort csrs
            "mtvec","pmpaddr0","pmpcfg0","mstatus","mepc","mscratch",
            "mcause","mtval","vl","vtype","sstatus", "mie"]:
            logging.debug("Ignoring: [%d]  [[%s]]" % (instr_cnt, line))
            pass
          elif "Warning (RISCV_" in line:
            logging.debug("Skipping: [%d] (%s) [[%s]]" %
                          (instr_cnt, prev_trace.instr_str, line))
            prev_trace.instr = "nop"
            prev_trace.instr_str = "nop"
          else:
            logging.debug("<unknown> (%s) in line: [%s] %s " %
                          (item, str(instr_cnt), line))
            if stop_on_first_error:
                fatal ("")
  logging.info("Processed instruction count : %d " % instr_cnt)
  if instr_cnt == 0:
    logging.error ("No Instructions in logfile: %s" % ovpsim_log)
    sys.exit(RET_FATAL)
  logging.info("CSV saved to : %s" % csv)

def main():
  """ if used standalone set up for testing """
  # Parse input arguments
  parser = argparse.ArgumentParser()
  parser.add_argument("--log", type=str, help="Input ovpsim simulation log")
  parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
  parser.add_argument("--full_trace", dest="full_trace",
                                         action="store_true",
                                         help="Generate the full trace")
  parser.add_argument("--verbose", dest="verbose", action="store_true",
                                         help="Verbose logging")
  parser.add_argument("--verbose2", dest="verbose2", action="store_true",
                                         help="Verbose logging detail 2")
  parser.add_argument("--stop_on_first_error", dest="stop_on_first_error",
                                         action="store_true",
                                         help="Stop on first error")
  parser.add_argument("--dont_truncate_after_first_ecall",
                                         dest="dont_truncate_after_first_ecall",
                                         action="store_true",
                                         help="Dont truncate on first ecall")
  parser.set_defaults(full_trace=False)
  parser.set_defaults(verbose=False)
  parser.set_defaults(verbose2=False)
  parser.set_defaults(stop_on_first_error=False)
  parser.set_defaults(dont_truncate_after_first_ecall=False)
  args = parser.parse_args()
  setup_logging(args.verbose)
  logging.debug("Logging Debug set")
  # Process ovpsim log
  process_ovpsim_sim_log(args.log, args.csv, args.full_trace,
    args.stop_on_first_error, args.dont_truncate_after_first_ecall,
    args.verbose2)


if __name__ == "__main__":
  main()

