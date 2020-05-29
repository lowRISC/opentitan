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
import utils
import random
import constraint
import riscv_directed_instr_lib


# Class riscv_instr_sequence for generating a single instruction sequence
# for a RISC-V assembly program.
class riscv_instr_sequence:

  def __init__(self, name):
    self.name = name
    self.instr_cnt = 0
    self.label_name = ""
    self.instr_stream = riscv_instr_stream.riscv_rand_instr_stream()
    self.instr_stack_enter = riscv_directed_instr_lib.riscv_push_stack_instr(
        "instr_stack_enter")  # Stack push instructions for sub-programs
    self.instr_stack_exit = riscv_directed_instr_lib.riscv_pop_stack_instr(
        "instr_stack_exit")  # Stack pop instructions for sub-programs
    self.is_main_program = 0
    self.program_stack_len = 0  # Stack space allocated for this program
    self.instr_string_list = []  # Save the instruction list
    self.directed_instr = [
    ]  # List of all directed instruction stream (elements of list are riscv_instr_stream)
    self.illegal_instr_pct = 0  # Percentage of illegal instructions
    self.hint_instr_pct = 0  # Percentage of hint instructions

  def gen_instr(self, is_main_program, enable_hint_instr=0):
    self.is_main_program = is_main_program
    # TODO: TO DO: cfg
    self.instr_stream.initialize_instr_list(self.instr_cnt)
    # Do not generate load/store instruction here
    # The load/store instruction will be inserted as directed instruction stream
    # For the below instruction, I need to add the hint_instr argument when we
    # support it (now it's 0 by default)
    self.instr_stream.gen_instr()
    if not is_main_program:
      self.gen_stack_enter_instr()
      self.gen_stack_exit_instr()

  # Generate the stack push operations for this program
  # It pushes the necessary context to the stack like RA, T0,loop registers etc. The stack
  # pointer(SP) is reduced by the amount the stack space allocated to this program.
  def gen_stack_enter_instr(self):
    # allow_branch = 1 for now as illegal/hint instructions are not supported yet
    allow_branch = 1
    # randomizing self.program_stack_len
    problem = constraint.Problem(constraint.MinConflictsSolver())
    # TO DO: cfg
    problem.addVariable("len", range(40, 65))

    # problem.addVariable('len', range(80, 128))
    def len_c(len):
      if len % 4 == 0:
        # if len % 8 == 0:
        return True

    problem.addConstraint(len_c, ["len"])
    self.program_stack_len = problem.getSolution()["len"]
    # TO DO: cfg
    # self.instr_stack_enter.cfg = cfg
    self.instr_stack_enter.push_start_label = self.label_name + "_stack_p"
    self.instr_stack_enter.gen_push_stack_instr(
        self.program_stack_len, allow_branch=allow_branch)
    self.instr_stream.instr_list = self.instr_stack_enter.instr_list + self.instr_stream.instr_list

  # Recover the saved GPR from the stack
  # Advance the stack pointer(SP) to release the allocated stack space.
  def gen_stack_exit_instr(self):
    # TO DO: cfg
    # self.instr_stack_exit.cfg = cfg
    self.instr_stack_exit.gen_pop_stack_instr(self.program_stack_len,
                                              self.instr_stack_enter.saved_regs)
    self.instr_stream.instr_list += self.instr_stack_exit.instr_list

  def generate_instr_stream(self):
    for i in range(len(self.instr_stream.instr_list)):
      if i == 0:
        temp_label = self.label_name + ":"
        prefix = "{:{}}".format(temp_label, utils.length)
        self.instr_stream.instr_list[i].has_label = 1
      else:
        if self.instr_stream.instr_list[i].has_label:
          # TODO: ugly
          temp_label = self.instr_stream.instr_list[i].label + ":"
          # prefix = "{:{}}".format(self.instr_stream.instr_list[i].label, utils.length)
          prefix = "{:{}}".format(temp_label, utils.length)
        else:
          prefix = "{}".format(utils.indent)
      if prefix != ":                 ":
        str = "{}{}".format(prefix,
                            self.instr_stream.instr_list[i].convert2asm())
        self.instr_string_list.append(str)
      else:
        str = "{}{}".format(utils.indent,
                            self.instr_stream.instr_list[i].convert2asm())
        self.instr_string_list.append(str)
    temp_label = "{}".format(len(self.instr_stream.instr_list) - 1) + ":"
    prefix = "{:{}}".format(temp_label, utils.length)
    if not self.is_main_program:
      str = "{}ret".format(prefix)
      self.instr_string_list.append(str)

  def post_process_instr(self):
    label_idx = 0
    branch_target = dict()
    for s in self.directed_instr:
      self.instr_stream.insert_instr_stream(s.instr_list)
    # Assign an index for all instructions, these indexes won't change even if a new instruction
    # is injected in the post process
    for item in self.instr_stream.instr_list:
      item.idx = label_idx
      # As of now there is no support for atomic instruction, so the second condition is always true
      if item.has_label and not item.atomic:
        if self.illegal_instr_pct > 0 and not item.is_illegal_instr:
          # The illegal instruction generator always increase PC by 4 when resume execution, need
          # to make sure PC + 4 is at the correct instruction boundary.
          if item.is_compressed:
            pass  # TODO: TO DO when we add the support for compressed instructions
        if self.hint_instr_pct > 0 and not item.is_illegal_instr:
          if item.is_compressed:
            pass  # TODO: TO DO when we add the support for compressed instructions
        item.label = "{}".format(label_idx)
        item.is_local_numeric_label = 1
        label_idx += 1
    # Generate branch target
    for item in self.instr_stream.instr_list:
      if item.solution[
          item.
          instr_category] == "BRANCH" and not item.branch_assigned and not item.is_illegal_instr:
        # Post process the branch instructions to give a valid local label
        # Here we only allow forward branch to avoid unexpected infinite loop
        # The loop structure will be inserted with a separate routine using
        # Reserved loop registers
        branch_byte_offset = 0
        branch_target_label = random.randint(item.idx + 1,
                                             min(label_idx - 1, item.idx +
                                                 20))  # TODO: TO DO need to do
        # the config class, here 20 is the max_branch_step
        item.imm_str = "{}f".format(branch_target_label)
        # Below calculation is only needed for generating the instruction stream in binary format
        for j in (self.instr_stream.instr_list.index(item) + 1,
                  len(self.instr_stream.instr_list) - 1):
          branch_byte_offset = branch_byte_offset + 2 if self.instr_stream.instr_list[
              j - 1].is_compressed else branch_byte_offset + 4
          if self.instr_stream.instr_list[j].label == "{}".format(
              branch_target_label):
            item.imm = branch_byte_offset
            break
          elif j == len(self.instr_stream.instr_list) - 1:
            # Cannot find target label
            pass
        item.branch_assigned = 1
        branch_target[branch_target_label] = 1
      # Remove the local label which is not used as branch target
      if item.has_label and item.is_local_numeric_label:
        idx = int(item.label)
        if not branch_target.get(idx):
          item.has_label = 0
    # Finished post-processing instructions

  # Inject a jump instruction stream
  # This function is called by riscv_asm_program_gen with the target program label
  # The jump routine is implemented with an atomic instruction stream(riscv_jump_instr). Similar
  # to load/store instructions, JALR/JAL instructions also need a proper base address and offset
  # as the jump target.
  def insert_jump_instr(self, target_label, idx):
    jump_instr = riscv_directed_instr_lib.riscv_jump_instr("jump_instr")
    jump_instr.target_program_label = target_label
    if not self.is_main_program:
      jump_instr.stack_exit_instr = self.instr_stack_exit.pop_stack_instr
    # TO DO: cfg
    # jump_instr.cfg = cfg
    jump_instr.label = self.label_name
    jump_instr.idx = idx

    jump_instr.problem_definition()
    jump_instr.randomize()

    self.instr_stream.insert_instr_stream(jump_instr.instr_list)
