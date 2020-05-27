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

import riscv_instr_stream
import riscv_instr_base
import random
import utils
import constraint


class riscv_directed_instr_stream(riscv_instr_stream.riscv_rand_instr_stream):

  def __init__(self, name=""):
    # calling super constructor
    riscv_instr_stream.riscv_rand_instr_stream.__init__(self)
    self.name = name

  def post_randomize(self):
    label = ""
    for instr in self.instr_list:
      instr.has_label = 0
      instr.atomic = 1
    # TO DO: check what is the returned value for get_name() func in SV
    self.instr_list[0].comment = "Start {}".format(self.name)
    self.instr_list[-1].comment = "End {}".format(self.name)
    if self.label != "":
      # self.instr_list[0].label = self.label
      self.instr_list[0].label = label
      self.instr_list[0].has_label = 1


# Jump instruction (JAL, JALR)
# la rd0, jump_tagert_label
# addi rd1, offset, rd0
# jalr rd, offset, rd1
# For JAL, restore the stack before doing the jump
class riscv_jump_instr(riscv_instr_stream.riscv_rand_instr_stream):

  def __init__(self, name):
    # calling super constructor
    riscv_instr_stream.riscv_rand_instr_stream.__init__(self)

    self.name = name
    self.jump = riscv_instr_base.riscv_instr_base("jump")
    self.addi = riscv_instr_base.riscv_instr_base("addi")
    self.la = riscv_instr_base.riscv_pseudo_instr("la")
    self.branch = riscv_instr_base.riscv_instr_base("branch")
    self.stack_exit_instr = []  # elements from type riscv_instr_base
    self.target_program_label = ""
    self.idx = 0
    self.solution = "A random solution which meets given constraints"
    self.problem = constraint.Problem(constraint.MinConflictsSolver())

    self.enable_branch = "Branch en/disabled"
    self.mixed_instr_cnt = "Number of mixed instructions"

  def problem_definition(self):
    self.la.problem_definition(la_instr=1)
    self.la.randomize()
    self.addi.problem_definition()

    def addi_c(name, rs1, rd, imm):
      # TO DO: cfg(reserved_regs)
      cond1 = name == "ADDI" and rs1 != "ZERO"
      cond2 = rs1 == self.la.solution[self.la.instr_rd]
      cond3 = rd == self.la.solution[self.la.instr_rd]
      # Avoid using negative offset -1024
      cond4 = imm != 0xFFFFFC00
      if cond1 and cond2 and cond3 and cond4:
        return True

    # Let's break the constraints, and see if it gets faster
    def addi_c_name(name):
      if name == "ADDI":
        return True

    def addi_c_rs1(rs1):
      if rs1 == self.la.solution[self.la.instr_rd] and rs1 != "ZERO":
        return True

    def addi_c_rd(rd):
      if rd == self.la.solution[self.la.instr_rd]:
        return True

    def addi_c_imm(imm):
      if imm != 0xFFFFFC00:
        return True

    self.addi.problem.addConstraint(addi_c_name, [self.addi.instr_name])
    self.addi.problem.addConstraint(addi_c_rs1, [self.addi.instr_src1])
    self.addi.problem.addConstraint(addi_c_rd, [self.addi.instr_rd])
    self.addi.problem.addConstraint(addi_c_imm, [self.addi.imm])
    self.addi.randomize()

    self.jump.problem.addVariable(self.jump.imm,
                                  [~(self.addi.solution[self.addi.imm]) + 1])
    self.jump.problem_definition()

    # let's break the constraints to multiple ones
    def jump_c(name, rd, rs1):
      cond1 = (name == "JAL" or name == "JALR") and rd == "RA"
      # cond2 = imm == ~(self.addi.solution[self.addi.imm])+1
      cond3 = rs1 == self.addi.solution[self.addi.instr_rd]
      if cond1 and cond3:
        return True

    def jump_c_name(name):
      if name == "JAL" or name == "JALR":
        return True

    def jump_c_rd(rd):
      if rd == "RA":
        return True

    def jump_c_rs1(rs1):
      if rs1 == self.addi.solution[self.addi.instr_rd]:
        return True

    self.jump.problem.addConstraint(jump_c_name, [self.jump.instr_name])
    self.jump.problem.addConstraint(jump_c_rd, [self.jump.instr_rd])
    self.jump.problem.addConstraint(jump_c_rs1, [self.jump.instr_src1])
    self.jump.randomize()

    self.branch.problem_definition()

    def branch_c(category):
      if category == "BRANCH":
        return True

    self.branch.problem.addConstraint(branch_c, [self.branch.instr_category])
    self.branch.randomize()

    self.problem.addVariable(self.enable_branch, [0, 1])
    self.problem.addVariable(self.mixed_instr_cnt, range(5, 11))

  def randomize(self):
    self.solution = self.problem.getSolution()
    self.post_randomize()

  def post_randomize(self):
    instr = []  # elements are from type riscv_instr_base
    # Generate some random instructions to mix with jump instructions
    self.reserved_rd = [self.addi.solution[self.addi.instr_src1]]
    self.initialize_instr_list(self.solution[self.mixed_instr_cnt])
    self.gen_instr(not_branch=1)
    self.la.imm_str = self.target_program_label
    # The branch instruction is always inserted right before the jump instruction to avoid
    # skipping other required instructions like restore stack, load jump base etc.
    # The purpose of adding the branch instruction here is to cover branch -> jump scenario.
    if self.enable_branch:
      instr = [self.branch]
    # Restore stack before unconditional jump
    if self.jump.solution[self.jump.instr_rd] == "ZERO":
      instr = self.stack_exit_instr + instr
    if self.jump.solution[self.jump.instr_name] == "JAL":
      self.jump.imm_str = self.target_program_label
    else:
      instr = [self.la, self.addi] + instr
    self.mix_instr_stream(instr)
    self.instr_list.append(self.jump)
    for item in self.instr_list:
      item.has_label = 0
      item.atomic = 1
    self.jump.has_label = 1
    self.jump.label = "j_{}_{}_{}".format(self.label, self.target_program_label,
                                          self.idx)
    self.branch.imm_str = self.jump.label
    self.branch.comment = "branch to jump instr"
    self.branch.branch_assigned = 1


# Push stack instruction stream
class riscv_push_stack_instr(riscv_instr_stream.riscv_rand_instr_stream):

  def __init__(self, name):
    # calling super constructor
    riscv_instr_stream.riscv_rand_instr_stream.__init__(self)

    self.name = name
    self.stack_len = 0
    self.num_of_reg_to_save = 0
    self.num_of_redudant_instr = 0
    self.push_stack_instr = []  # elements are from type riscv_instr_base
    self.saved_regs = []  # elements are from type riscv_reg_t
    self.push_start_label = ""

    self.branch_instr = riscv_instr_base.riscv_instr_base("branch_instr")
    self.enable_branch = 0

  def init(self):
    # Save RA, T0 and all reserved loop regs
    # TO DO: cfg. Note: loops are not supported yet
    self.saved_regs = ["RA", "T0"]
    self.num_of_reg_to_save = len(self.saved_regs)
    self.num_of_redudant_instr = random.randint(3, 10)
    self.initialize_instr_list(self.num_of_redudant_instr)

  def gen_push_stack_instr(self, stack_len, allow_branch=1):
    self.stack_len = stack_len
    self.init()
    self.gen_instr(not_branch=1)
    self.push_stack_instr = [None] * (self.num_of_reg_to_save + 1)
    for i in range(len(self.push_stack_instr)):
      self.push_stack_instr[i] = riscv_instr_base.riscv_instr_base(
          "push_stack_instr_{}".format(i))
    # addi sp,sp,-imm
    # To help the constraint solver, we can specify the imm value in the
    # begginning, instead of applying two constraints on top of each other.
    # In the instr_base, we can add the imm var if it's not been already added
    self.push_stack_instr[0].problem.addVariable(self.push_stack_instr[0].imm,
                                                 [~self.stack_len + 1])
    self.push_stack_instr[0].problem_definition()

    # stack_length = self.stack_len
    def addi_c(name, rd, rs1):
      cond1 = name == "ADDI"
      cond2 = rd == "SP"
      cond3 = rs1 == "SP"
      # cond4 = imm == ~stack_length + 1
      if cond1 and cond2 and cond3:
        return True

    # breaking it to multiple constraints would fasten the constraint solver
    def addi_c_name(name):
      if name == "ADDI":
        return True

    def addi_c_rd(rd):
      if rd == "SP":
        return True

    def addi_c_rs1(rs1):
      if rs1 == "SP":
        return True

    self.push_stack_instr[0].problem.addConstraint(
        addi_c_name, [self.push_stack_instr[0].instr_name])
    self.push_stack_instr[0].problem.addConstraint(
        addi_c_rd, [self.push_stack_instr[0].instr_rd])
    self.push_stack_instr[0].problem.addConstraint(
        addi_c_rs1, [self.push_stack_instr[0].instr_src1])
    self.push_stack_instr[0].randomize()
    self.push_stack_instr[0].imm_str = "-{}".format(self.stack_len)
    for i in range(len(self.saved_regs)):
      # TO DO: XLEN in core_setting
      if utils.XLEN == 32:
        self.push_stack_instr[i + 1].problem.addVariable(
            self.push_stack_instr[i + 1].imm, [4 * (i + 1)])
        self.push_stack_instr[i + 1].problem_definition(no_load_store=0)
        tmp_reg = self.saved_regs[i]

        def instr_c(name, rs1, rs2):
          cond1 = name == "SW"
          cond2 = rs2 == tmp_reg
          cond3 = rs1 == "SP"
          # cond4 = imm == 4 * (i + 1)
          if cond1 and cond2 and cond3:
            return True

        def instr_c_name(name):
          if name == "SW":
            return True

        def instr_c_rs2(rs2):
          if rs2 == tmp_reg:
            return True

        def instr_c_rs1(rs1):
          if rs1 == "SP":
            return True

        self.push_stack_instr[i + 1].problem.addConstraint(
            instr_c_name, [self.push_stack_instr[i + 1].instr_name])
        self.push_stack_instr[i + 1].problem.addConstraint(
            instr_c_rs1, [self.push_stack_instr[i + 1].instr_src1])
        self.push_stack_instr[i + 1].problem.addConstraint(
            instr_c_rs2, [self.push_stack_instr[i + 1].instr_src2])
        self.push_stack_instr[i + 1].randomize()
      else:
        self.push_stack_instr[i + 1].problem_definition(no_load_store=0)
        tmp_reg = self.saved_regs[i]

        def instr_c(name, rs1, rs2, imm):
          cond1 = name == "SD"
          cond2 = rs2 == tmp_reg
          cond3 = rs1 == "SP"
          cond4 = imm == 8 * (i + 1)
          if cond1 and cond2 and cond3 and cond4:
            return True

        self.push_stack_instr[i + 1].problem.addConstraint(
            instr_c, [
                self.push_stack_instr[i + 1].instr_name,
                self.push_stack_instr[i + 1].instr_src1,
                self.push_stack_instr[i + 1].instr_src2,
                self.push_stack_instr[i + 1].imm
            ])
        self.push_stack_instr[i + 1].randomize()
      self.push_stack_instr[i + 1].process_load_store = 0
    if allow_branch:
      self.enable_branch = random.randint(0, 1)
    else:
      self.enable_branch = 0
    if self.enable_branch:
      # Cover jal -> branch scenario, the branch is added before push stack operation
      self.branch_instr.problem_definition()

      def branch_c(category):
        if category == "BRANCH":
          return True

      self.branch_instr.problem.addConstraint(
          branch_c, [self.branch_instr.instr_category])
      self.branch_instr.randomize()
      self.branch_instr.imm_str = self.push_start_label
      self.branch_instr.branch_assigned = 1
      self.push_stack_instr[0].label = self.push_start_label
      self.push_stack_instr[0].has_label = 1
      self.push_stack_instr = [self.branch_instr] + self.push_stack_instr
    self.mix_instr_stream(self.push_stack_instr)
    for i in range(len(self.instr_list)):
      self.instr_list[i].atomic = 1
      if self.instr_list[i].label == "":
        self.instr_list[i].has_label = 0


# Pop stack instruction stream
class riscv_pop_stack_instr(riscv_instr_stream.riscv_rand_instr_stream):

  def __init__(self, name):
    # calling super constructor
    riscv_instr_stream.riscv_rand_instr_stream.__init__(self)

    self.name = name
    self.stack_len = 0
    self.num_of_reg_to_save = 0
    self.num_of_redudant_instr = 0
    self.pop_stack_instr = []  # elements are from type riscv_instr_base
    self.saved_regs = []  # elements are from type riscv_reg_t

  def init(self):
    self.num_of_reg_to_save = len(self.saved_regs)
    self.num_of_redudant_instr = random.randint(3, 10)
    self.initialize_instr_list(self.num_of_redudant_instr)

  def gen_pop_stack_instr(self, stack_len, saved_regs):
    self.stack_len = stack_len
    self.saved_regs = saved_regs
    self.init()
    self.gen_instr(not_branch=1)
    self.pop_stack_instr = [None] * (self.num_of_reg_to_save + 1)
    for i in range(len(self.pop_stack_instr)):
      self.pop_stack_instr[i] = riscv_instr_base.riscv_instr_base(
          "pop_stack_instr_{}".format(i))
    for i in range(len(self.saved_regs)):
      # TO DO: XLEN in core_setting
      if utils.XLEN == 32:
        self.pop_stack_instr[i].problem.addVariable(self.pop_stack_instr[i].imm,
                                                    [4 * (i + 1)])
        self.pop_stack_instr[i].problem_definition(no_load_store=0)

        # breaking a complex constraint to multiple simple constraints fastens the constraint solver
        def instr_c(name, rd, rs1):
          cond1 = name == "LW"
          cond2 = rd == self.saved_regs[i]
          cond3 = rs1 == "SP"
          # cond4 = imm == 4 * (i + 1)
          if cond1 and cond2 and cond3:
            return True

        def instr_c_name(name):
          if name == "LW":
            return True

        def instr_c_rd(rd):
          if rd == self.saved_regs[i]:
            return True

        def instr_c_rs1(rs1):
          if rs1 == "SP":
            return True

        self.pop_stack_instr[i].problem.addConstraint(
            instr_c_name, [self.pop_stack_instr[i].instr_name])
        self.pop_stack_instr[i].problem.addConstraint(
            instr_c_rd, [self.pop_stack_instr[i].instr_rd])
        self.pop_stack_instr[i].problem.addConstraint(
            instr_c_rs1, [self.pop_stack_instr[i].instr_src1])
        self.pop_stack_instr[i].randomize()
      else:
        self.pop_stack_instr[i].problem_definition(no_load_store=0)

        def instr_c(name, rd, rs1, imm):
          cond1 = name == "LD"
          cond2 = rd == self.saved_regs[i]
          cond3 = rs1 == "SP"
          cond4 = imm == 8 * (i + 1)
          if cond1 and cond2 and cond3 and cond4:
            return True

        self.pop_stack_instr[i].problem.addConstraint(instr_c, [
            self.pop_stack_instr[i].instr_name,
            self.pop_stack_instr[i].instr_rd,
            self.pop_stack_instr[i].instr_src1, self.pop_stack_instr[i].imm
        ])
        self.pop_stack_instr[i].randomize()
      self.pop_stack_instr[i].process_load_store = 0
    # addi sp,sp,imm
    self.pop_stack_instr[self.num_of_reg_to_save].problem.addVariable(
        self.pop_stack_instr[self.num_of_reg_to_save].imm, [self.stack_len])
    self.pop_stack_instr[self.num_of_reg_to_save].problem_definition()

    # stack_length = self.stack_len
    def addi_c(name, rd, rs1):
      cond1 = name == "ADDI"
      cond2 = rd == "SP"
      cond3 = rs1 == "SP"
      # cond4 = imm == stack_length
      if cond1 and cond2 and cond3:
        return True

    def addi_c_name(name):
      if name == "ADDI":
        return True

    def addi_c_rd(rd):
      if rd == "SP":
        return True

    def addi_c_rs1(rs1):
      if rs1 == "SP":
        return True

    tmp_instr = self.pop_stack_instr[self.num_of_reg_to_save]
    self.pop_stack_instr[self.num_of_reg_to_save].problem.addConstraint(
        addi_c_name, [self.pop_stack_instr[self.num_of_reg_to_save].instr_name])
    self.pop_stack_instr[self.num_of_reg_to_save].problem.addConstraint(
        addi_c_rd, [self.pop_stack_instr[self.num_of_reg_to_save].instr_rd])
    self.pop_stack_instr[self.num_of_reg_to_save].problem.addConstraint(
        addi_c_rs1, [self.pop_stack_instr[self.num_of_reg_to_save].instr_src1])
    self.pop_stack_instr[self.num_of_reg_to_save].randomize()
    self.pop_stack_instr[self.num_of_reg_to_save].imm_str = "{}".format(
        self.stack_len)
    self.mix_instr_stream(self.pop_stack_instr)
    for item in self.instr_list:
      item.atomic = 1
      item.has_label = 0
