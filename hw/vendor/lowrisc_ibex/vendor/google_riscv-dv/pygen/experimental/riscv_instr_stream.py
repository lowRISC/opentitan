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

import riscv_instr_base
import riscv_rand_instr
import random
import constraint


class riscv_instr_stream:

  def __init__(self):
    self.instr_list = []
    self.instr_cnt = 0
    self.label = ""

  def initialize_instr_list(self, instr_cnt):
    self.instr_list = []
    self.instr_cnt = instr_cnt
    self.create_instr_instance()

  def create_instr_instance(self):
    for i in range(self.instr_cnt):
      instr = riscv_instr_base.riscv_instr_base()
      self.instr_list.append(instr)

  # Insert an instruction to the existing instruction stream at the given index
  # When index is -1, the instruction is injected at a random location
  # When replace is 1, the original instruction at the inserted position will be replaced
  def insert_instr_stream(self, new_instr, idx=-1, replace=0):
    current_instr_cnt = len(self.instr_list)
    new_instr_cnt = len(new_instr)
    if idx == -1:
      idx = random.randint(0, current_instr_cnt - 1)
      # cares must be taken to avoid targeting an atomic instruction (while atomic, find a new idx)
      while self.instr_list[idx].atomic:
        idx = random.randint(0, current_instr_cnt - 1)
    elif idx > current_instr_cnt or idx < 0:
      # TODO: Print an error indicating that inserting an instruction in this location is not possible
      pass
    # When replace is 1, the original instruction at this index will be removed. The label of the
    # original instruction will be copied to the head of inserted instruction stream.
    if replace == 1:
      new_instr[0].label = self.instr_list[idx].label
      new_instr[0].has_label = self.instr_list[idx].has_label
      self.instr_list = self.instr_list[0:idx] + new_instr + self.instr_list[
          idx + 1:current_instr_cnt]
    else:
      self.instr_list = self.instr_list[0:idx] + new_instr + self.instr_list[
          idx:current_instr_cnt]

  # Mix the input instruction stream with the original instruction, the instruction order is
  # preserved. When 'contained' is set, the original instruction stream will be inside the
  # new instruction stream with the first and last instruction from the input instruction stream.
  # new_instr is a list of riscv_instr_base
  def mix_instr_stream(self, new_instr, contained=0):
    current_instr_cnt = len(self.instr_list)
    new_instr_cnt = len(new_instr)
    insert_instr_position = [None] * new_instr_cnt
    for i in range(new_instr_cnt):
      insert_instr_position[i] = i
    problem = constraint.Problem(constraint.MinConflictsSolver())
    problem.addVariables(insert_instr_position, range(current_instr_cnt))

    def problem_c(current, previous):
      if current >= previous:
        return True

    for i in range(1, len(insert_instr_position)):
      problem.addConstraint(
          problem_c, [insert_instr_position[i], insert_instr_position[i - 1]])
    sol = problem.getSolution()
    if contained:
      sol[0] = 0
      if new_instr_cnt > 1:
        sol[new_instr_cnt - 1] = current_instr_cnt - 1
    for i in range(len(new_instr)):
      self.insert_instr(new_instr[i], sol[i] + i)

  # Insert an instruction to the existing instruction stream at the given index
  # When index is -1, the instruction is injected at a random location
  def insert_instr(self, instr, idx=-1):
    current_instr_cnt = len(self.instr_list)
    if idx == -1:
      idx = random.randint(0, current_instr_cnt - 1)
      while self.instr_list[idx].atomic:
        idx = random.randint(0, current_instr_cnt - 1)
    elif idx > current_instr_cnt or idx < 0:
      # TO DO: print an error
      print("Error!")
    self.instr_list.insert(idx, instr)


class riscv_rand_instr_stream(riscv_instr_stream):

  def __init__(self):
    # calling super constructor
    riscv_instr_stream.__init__(self)
    # TO DO: cfg
    self.access_u_mode_mem = 1
    self.max_load_store_offset = 4096
    self.max_data_page_id = 40
    self.reserved_rd = []

  # constraint for some additional reserved registers that should not be used as rd register
  # by this instruction stream (we want to add another constraint to the riscv_rand_instr from here
  # In fact, we want to add another constraint after we call problem_definition in gen_instr)
  def avoid_reserved_rd_c(self, instr):
    if len(self.reserved_rd) > 0:

      def rd_c(rd):
        if rd not in self.reserved_rd:
          return True

      instr.problem.addConstraint(rd_c, [instr.instr_rd])

  def create_instr_instance(self):
    for i in range(self.instr_cnt):
      instr = riscv_rand_instr.riscv_rand_instr()
      # TO DO: cfg
      instr.reserved_rd = self.reserved_rd
      self.instr_list.append(instr)

  def pre_randomize(self):
    if self.access_u_mode_mem:
      # TO DO: riscv core setting
      self.max_load_store_offset = utils.data_page_size
      self.max_data_page_id = utils.num_of_data_pages
    else:
      pass
    # kernel is not supported yet
    # self.max_load_store_offset = utils.kernel_data_page_size
    # self.max_data_page_id = utils.num_of_kernel_data_pages

  def gen_instr(self, not_branch=0):
    for item in self.instr_list[:-1]:
      item.problem_definition(no_branch=not_branch)
      self.avoid_reserved_rd_c(item)
      item.randomize()
    # for the last one, it shouldn't be a branch instruction (as there is no
    # forward branch possibility for the last instruction
    if len(self.instr_list) > 0:
      self.instr_list[-1].problem_definition(no_branch=1)
      self.avoid_reserved_rd_c(self.instr_list[-1])
      self.instr_list[-1].randomize()
