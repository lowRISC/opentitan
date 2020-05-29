"""Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

import utils
import random
import constraint
from bitstring import BitArray, BitStream


class riscv_instr_base:
  max_instr_length = 11

  # Missing parts: latency

  def __init__(self, name=""):
    self.name = name
    self.instr_group = "Instruction Group"
    self.instr_format = "Instruction Format"
    self.instr_category = "Instruction Category"
    self.instr_name = "Instruction Name"
    self.instr_imm_t = "Instruction Immediate Type"
    self.instr_src2 = "Instruction Source 2"
    self.instr_src1 = "Instruction Source 1"
    self.instr_rd = "Instruction Destination"
    self.imm = "Instruction Immediate"
    self.imm_length = "Instruction Immediate Length"
    self.imm_str = ""
    self.csr = "CSR"
    self.comment = ""
    self.has_label = 1
    self.label = ""
    self.idx = -1
    self.atomic = 0  # As of now, we don't support atomic instructions.
    self.is_compressed = 0  # As of now, compressed instructions are not supported
    self.is_illegal_instr = 0
    self.is_local_numeric_label = 0
    self.is_pseudo_instr = "Is it a pseudo instruction or not"
    self.branch_assigned = 0
    self.process_load_store = 1
    self.solution = "A random solution which meets given constraints"
    self.problem = constraint.Problem(constraint.MinConflictsSolver())

  # Convert an instruction to its assembly form.
  def convert2asm(self):
    asm = name = self.solution[self.instr_name]
    format = self.solution[self.instr_format]
    category = self.solution[self.instr_category]
    src2 = self.solution[self.instr_src2]
    src1 = self.solution[self.instr_src1]
    destination = self.solution[self.instr_rd]
    csr = self.solution[self.csr]

    if category != "SYSTEM":
      if format == "J_FORMAT" or format == "U_FORMAT":
        asm += " {}, {}".format(destination, self.get_imm())
      elif format == "I_FORMAT":
        if name == "NOP":
          asm = "nop"
        elif name == "FENCE":
          asm = "fence"
        elif name == "FENCEI":
          asm = "fence.i"
        elif category == "LOAD":
          asm += " {}, {}({})".format(destination, self.get_imm(), src1)
        elif category == "CSR":
          asm += " {}, {}, {}".format(destination, hex(csr), self.get_imm())
        else:
          asm += " {}, {}, {}".format(destination, src1, self.get_imm())
      elif format == "S_FORMAT" or format == "B_FORMAT":
        if category == "STORE":
          asm += " {}, {}({})".format(src2, self.get_imm(), src1)
        else:
          asm += " {}, {}, {}".format(src1, src2, self.get_imm())
      elif format == "R_FORMAT":
        if category == "CSR":
          asm += " {}, {}, {}".format(destination, hex(csr), src1)
        else:
          asm += " {}, {}, {}".format(destination, src1, src2)
    else:
      if name == "BREAK":
        asm = ".option norvc;ebreak;.option rvc;"
    if self.comment != "":
      asm += " # {}".format(self.comment)
    return asm.lower()

  # Instruction to binary format
  # TODO: to do
  def convert2bin(self, sol):
    name = sol[self.instr_name]
    format = sol[self.instr_format]
    imm = sol[self.imm]
    rd = sol[self.instr_rd]
    if format == "J_FORMAT":
      binary = ""

  def post_randomize(self):
    imm_length = self.solution[self.imm_length]
    imm_t = self.solution[self.instr_imm_t]
    imm = self.solution[self.imm]
    imm_bit = BitArray(int=imm, length=32)
    imm_mask = BitArray(uint=4294967295, length=32)
    imm_mask = imm_mask << imm_length
    if imm_t == "UIMM" or imm_t == "NZUIMM":
      imm_bit = imm_bit & ~imm_mask
      imm = imm_bit.int
    else:
      if imm_bit[-imm_length]:
        imm_bit = imm_bit | imm_mask
        imm = imm_bit.int
      else:
        imm_bit = imm_bit & ~imm_mask
        imm = imm_bit.int

    if (imm_t == "NZIMM" or imm_t == "NZUIMM") and imm == 0:
      imm = random.randrange(1, 2**(imm_length - 1) - 1)
    if self.imm_str == "":
      self.imm_str = int(imm)

  def get_imm(self):
    return self.imm_str

  def problem_definition(self,
                         no_branch=0,
                         no_load_store=1,
                         enable_hint_instr=0,
                         no_name_c=0):
    # Adding variables to the problem
    self.problem.addVariable(self.instr_group, utils.riscv_instr_group_t)
    self.problem.addVariable(self.instr_format, utils.riscv_instr_format_t)
    self.problem.addVariable(self.instr_category, utils.riscv_instr_category_t)
    self.problem.addVariable(self.instr_name, utils.riscv_instr_name_t)
    self.problem.addVariable(self.instr_imm_t, utils.imm_t)
    self.problem.addVariables([self.instr_src2, self.instr_src1, self.instr_rd],
                              utils.riscv_reg_t)
    self.problem.addVariable(self.imm_length, [5, 6, 8, 11, 20])
    # problem.addVariable(self.imm, range(0x00000000, 0xffffffff)) # doesn't
    # work because: OverflowError: Python int too large to convert to C ssize_t
    # Need to change the constraint to a soft constraint, as the default_c in
    # the pseudo instruction class is in conflict with this one
    if self.imm not in self.problem._variables:
      self.problem.addVariable(self.imm, range(0x0000, 0xffff))
    self.problem.addVariable(self.csr, range(0x000, 0xfff))

    def default_c(is_pseudo_instr):
      if not is_pseudo_instr:
        return True

    def name_c(name, group, format, category, imm_t):
      condition = (
          # Load instructions
          (name == "LB" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOAD" and imm_t == "IMM") or
          (name == "LH" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOAD" and imm_t == "IMM") or
          (name == "LW" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOAD" and imm_t == "IMM") or
          (name == "LBU" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOAD" and imm_t == "IMM") or
          (name == "LHU" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOAD" and imm_t == "IMM")
          # Store instructions
          or (name == "SB" and group == "RV32I" and format == "S_FORMAT" and
              category == "STORE" and imm_t == "IMM") or
          (name == "SH" and group == "RV32I" and format == "S_FORMAT" and
           category == "STORE" and imm_t == "IMM") or
          (name == "SW" and group == "RV32I" and format == "S_FORMAT" and
           category == "STORE" and imm_t == "IMM")
          # Shift istructions
          or (name == "SLL" and group == "RV32I" and format == "R_FORMAT" and
              category == "SHIFT" and imm_t == "IMM") or
          (name == "SLLI" and group == "RV32I" and format == "I_FORMAT" and
           category == "SHIFT" and imm_t == "IMM") or
          (name == "SRL" and group == "RV32I" and format == "R_FORMAT" and
           category == "SHIFT" and imm_t == "IMM") or
          (name == "SRLI" and group == "RV32I" and format == "I_FORMAT" and
           category == "SHIFT" and imm_t == "IMM") or
          (name == "SRA" and group == "RV32I" and format == "R_FORMAT" and
           category == "SHIFT" and imm_t == "IMM") or
          (name == "SRAI" and group == "RV32I" and format == "I_FORMAT" and
           category == "SHIFT" and imm_t == "IMM")
          # Arithmetic instructions
          or (name == "ADD" and group == "RV32I" and format == "R_FORMAT" and
              category == "ARITHMETIC" and imm_t == "IMM") or
          (name == "ADDI" and group == "RV32I" and format == "I_FORMAT" and
           category == "ARITHMETIC" and imm_t == "IMM") or
          (name == "NOP" and group == "RV32I" and format == "I_FORMAT" and
           category == "ARITHMETIC" and imm_t == "IMM") or
          (name == "SUB" and group == "RV32I" and format == "R_FORMAT" and
           category == "ARITHMETIC" and imm_t == "IMM") or
          (name == "LUI" and group == "RV32I" and format == "U_FORMAT" and
           category == "ARITHMETIC" and imm_t == "UIMM") or
          (name == "AUIPC" and group == "RV32I" and format == "U_FORMAT" and
           category == "ARITHMETIC" and imm_t == "UIMM")
          # Logical instructions
          or (name == "XOR" and group == "RV32I" and format == "R_FORMAT" and
              category == "LOGICAL" and imm_t == "IMM") or
          (name == "XORI" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOGICAL" and imm_t == "IMM") or
          (name == "OR" and group == "RV32I" and format == "R_FORMAT" and
           category == "LOGICAL" and imm_t == "IMM") or
          (name == "ORI" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOGICAL" and imm_t == "IMM") or
          (name == "AND" and group == "RV32I" and format == "R_FORMAT" and
           category == "LOGICAL" and imm_t == "IMM") or
          (name == "ANDI" and group == "RV32I" and format == "I_FORMAT" and
           category == "LOGICAL" and imm_t == "IMM")
          # Compare instructions
          or (name == "SLT" and group == "RV32I" and format == "R_FORMAT" and
              category == "COMPARE" and imm_t == "IMM") or
          (name == "SLTI" and group == "RV32I" and format == "I_FORMAT" and
           category == "COMPARE" and imm_t == "IMM") or
          (name == "SLTU" and group == "RV32I" and format == "R_FORMAT" and
           category == "COMPARE" and imm_t == "IMM") or
          (name == "SLTIU" and group == "RV32I" and format == "I_FORMAT" and
           category == "COMPARE" and imm_t == "IMM")
          # Branch instructions
          or (name == "BEQ" and group == "RV32I" and format == "B_FORMAT" and
              category == "BRANCH" and imm_t == "IMM") or
          (name == "BNE" and group == "RV32I" and format == "B_FORMAT" and
           category == "BRANCH" and imm_t == "IMM") or
          (name == "BLT" and group == "RV32I" and format == "B_FORMAT" and
           category == "BRANCH" and imm_t == "IMM") or
          (name == "BGE" and group == "RV32I" and format == "B_FORMAT" and
           category == "BRANCH" and imm_t == "IMM") or
          (name == "BLTU" and group == "RV32I" and format == "B_FORMAT" and
           category == "BRANCH" and imm_t == "IMM") or
          (name == "BGEU" and group == "RV32I" and format == "B_FORMAT" and
           category == "BRANCH" and imm_t == "IMM")
          # Jump instructions
          or (name == "JAL" and group == "RV32I" and format == "J_FORMAT" and
              category == "JUMP" and imm_t == "IMM") or
          (name == "JALR" and group == "RV32I" and format == "I_FORMAT" and
           category == "JUMP" and imm_t == "IMM")
          # Synch instructions
          or (name == "FENCE" and group == "RV32I" and format == "I_FORMAT" and
              category == "SYNCH" and imm_t == "IMM") or
          (name == "FENCEI" and group == "RV32I" and format == "I_FORMAT" and
           category == "SYNCH" and imm_t == "IMM")
          # System instructions
          or (name == "ECALL" and group == "RV32I" and format == "I_FORMAT" and
              category == "SYSTEM" and imm_t == "IMM") or
          (name == "EBREAK" and group == "RV32I" and format == "I_FORMAT" and
           category == "SYSTEM" and imm_t == "IMM") or
          (name == "URET" and group == "RV32I" and format == "I_FORMAT" and
           category == "SYSTEM" and imm_t == "IMM") or
          (name == "SRET" and group == "RV32I" and format == "I_FORMAT" and
           category == "SYSTEM" and imm_t == "IMM") or
          (name == "MRET" and group == "RV32I" and format == "I_FORMAT" and
           category == "SYSTEM" and imm_t == "IMM") or
          (name == "WFI" and group == "RV32I" and format == "I_FORMAT" and
           category == "SYSTEM" and imm_t == "IMM")
          # CSR instructions
          or (name == "CSRRW" and group == "RV32I" and format == "R_FORMAT" and
              category == "CSR" and imm_t == "UIMM") or
          (name == "CSRRS" and group == "RV32I" and format == "R_FORMAT" and
           category == "CSR" and imm_t == "UIMM") or
          (name == "CSRRC" and group == "RV32I" and format == "R_FORMAT" and
           category == "CSR" and imm_t == "UIMM") or
          (name == "CSRRWI" and group == "RV32I" and format == "I_FORMAT" and
           category == "CSR" and imm_t == "UIMM") or
          (name == "CSRRSI" and group == "RV32I" and format == "I_FORMAT" and
           category == "CSR" and imm_t == "UIMM") or
          (name == "CSRRCI" and group == "RV32I" and format == "I_FORMAT" and
           category == "CSR" and imm_t == "UIMM"))
      if condition:
        return True

    def fence_c(name, source1, destination, imm):
      if name == "FENCE" or name == "FENCEI":
        if source1 == "ZERO" and destination == "ZERO" and imm == 0:
          return True
      else:
        return True

    def load_store_c(category, source1):
      if category == "LOAD" or category == "STORE":
        if source1 != "ZERO":
          return True
      else:
        return True

    def nop_c(name, source1, source2, destination):
      if name == "NOP":
        if source1 == "ZERO" and source2 == "ZERO" and destination == "ZERO":
          return True
      else:
        return True

    def system_instr_c(category, source1, destination):
      if category == "SYSTEM" or category == "SYNCH":
        if source1 == "ZERO" and destination == "ZERO":
          return True
      else:
        return True

    def imm_len_c(format, imm_t, imm_length):
      if format == "U_FORMAT" or format == "J_FORMAT":
        return imm_length == 20
      elif format == "I_FORMAT" or format == "S_FORMAT" or format == "B_FORMAT":
        if imm_t == "UIMM":
          return imm_length == 5
        else:
          return imm_length == 11
      else:
        return True

    def imm_val_c(imm_type, imm):
      if imm_type == "NZIMM" or imm_type == "NZUIMM":
        return imm != 0
      else:
        return True

    def shift_imm_val_c(category, imm):
      if category == "SHIFT":
        return imm < utils.XLEN
      else:
        return True

    def only_arithmetic_and_logical_c(category):
      if category == "ARITHMETIC" or category == "LOGICAL" or  \
         category == "BRANCH" or category == "LOAD" or category == "STORE":
        return True

    def non_system(category):
      if category != "SYSTEM":
        return True

    def non_csr(category):
      if category != "CSR":
        return True

    def non_synch(category):
      if category != "SYNCH":
        return True

    def no_branch_c(category):
      if category != "BRANCH":
        return True

    def no_load_store_c(category):
      if category != "LOAD" and category != "STORE":
        return True

    # Refer to pseudo class for explanation
    if not no_name_c:
      self.problem.addConstraint(name_c, [
          self.instr_name, self.instr_group, self.instr_format,
          self.instr_category, self.instr_imm_t
      ])
    # TODO: add a temporarily constraint for generating only arithmetic random instructions
    # self.problem.addConstraint(only_arithmetic_and_logical_c, [self.instr_category])
    # self.problem.addConstraint(default_c, [self.is_pseudo_instr])
    self.problem.addConstraint(non_csr, [self.instr_category])
    self.problem.addConstraint(non_system, [self.instr_category])
    self.problem.addConstraint(non_synch, [self.instr_category])

    if no_branch:
      self.problem.addConstraint(no_branch_c, [self.instr_category])
    if no_load_store:
      self.problem.addConstraint(no_load_store_c, [self.instr_category])

    self.problem.addConstraint(
        fence_c, [self.instr_name, self.instr_src1, self.instr_rd, self.imm])
    self.problem.addConstraint(load_store_c,
                               [self.instr_category, self.instr_src1])
    self.problem.addConstraint(
        nop_c,
        [self.instr_name, self.instr_src1, self.instr_src2, self.instr_rd
        ])  #: takes too long, don't know why
    self.problem.addConstraint(
        system_instr_c, [self.instr_category, self.instr_src1, self.instr_rd])
    self.problem.addConstraint(
        imm_len_c, [self.instr_format, self.instr_imm_t, self.imm_length])
    self.problem.addConstraint(imm_val_c, [self.instr_imm_t, self.imm])
    self.problem.addConstraint(shift_imm_val_c, [self.instr_category, self.imm])
    # return
    # return self.problem.getSolution()

  def randomize(self):
    # old randomize()
    # self.solution = self.problem.getSolution()
    # self.post_randomize()

    self.solution = self.problem.getSolution()
    if self.solution:
      # print("TODO: randomized with steps: {}".format(self.problem._solver._steps))
      pass
    else:
      i = 1
      while self.solution is None:
        for j in range(10):
          self.solution = self.problem.getSolution()
          if self.solution:
            # print("TODO: randomized with steps: {}".format(self.problem._solver._steps))
            break
        i *= 5
        self.problem._solver._steps *= i
    self.post_randomize()


# Psuedo instructions are used to simplify assembly program writing
class riscv_pseudo_instr(riscv_instr_base):

  def __init__(self, name=""):
    # calling super constructor
    riscv_instr_base.__init__(self, name)
    # Important: Constraint solver gets too slow in pseudo class. We have three solutions:
    # 1- change the type of the constraint solver, from MinConflict to regular, this one
    # also takes fairly good amount of time, but it's good for validity check, to see
    # if constraints are valid and there is no conflict between them.
    # 2- Increase the number of steps for MinConflict...
    # 3- Since we don't need to check the name_c constraint here, we can get rid of it
    # for pseudo class! We're going to use this option for now
    # self.problem = constraint.Problem(constraint.MinConflictsSolver(steps=10000))
    # self.problem = constraint.Problem()
    self.process_load_store = 0
    self.pseudo_instr_name = "Pseudo instruction name"

  def problem_definition(self, la_instr=0):
    # Calling the super problem_definition, to apply all the constraints to the base object
    # super().problem_definition(no_load_store=0, no_name_c=1)
    super().problem_definition(no_load_store=0)
    # To add the new constraint carried by the problem_definition
    # fun()
    self.problem.addVariable(self.pseudo_instr_name,
                             utils.riscv_pseudo_instr_name_t)
    self.problem.addVariable(self.is_pseudo_instr, range(2))

    def pseudo_name_c(name, group, format, category):
      condition = (((name == "LI" or name == "LA") and group == "RV32I" and
                    format == "I_FORMAT" and category == "LOAD"))
      if condition:
        return True

    def la_c(name):
      if name == "LA":
        return True

    def default_c(is_pseudo_instr):
      if is_pseudo_instr:
        return True

    self.problem.addConstraint(pseudo_name_c, [
        self.pseudo_instr_name, self.instr_group, self.instr_format,
        self.instr_category
    ])
    if la_instr:
      self.problem.addConstraint(la_c, [self.pseudo_instr_name])
    self.problem.addConstraint(default_c, [self.is_pseudo_instr])

    return

  # Convert the instruction to assembly code
  def convert2asm(self):
    asm_str = self.get_instr_name()
    destination = self.solution[self.instr_rd]
    # instr rd,imm
    asm_str = "{} {}, {}".format(asm_str, destination, self.get_imm())
    if self.comment != "":
      asm_str = asm_str + " #" + self.comment
    return asm_str.lower()

  def get_instr_name(self):
    return self.solution[self.pseudo_instr_name]
