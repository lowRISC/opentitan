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

import riscv_directed_instr_lib
import riscv_instr_base
import constraint
import riscv_rand_instr
import random
import utils


# Base class for all load/store instruction stream
class riscv_load_store_base_instr_stream(
    riscv_directed_instr_lib.riscv_directed_instr_stream):

  def __init__(self, name):
    # calling super constructor
    riscv_directed_instr_lib.riscv_directed_instr_stream.__init__(self, name)
    # New attributes dedicated to load_store_instr_stream
    # we have a separate problem for num_load_store, as we want to have offset
    # and addr with the length of num_load_store
    self.num_load_store = "Number of loads/stores"
    # self.num_load_store = random.randint(0, 65536)
    # self.num_load_store = random.randint(0, 32)
    self.num_mixed_instr = "Number of mixed instructions"
    self.base = "Base address for load/store"
    self.offset = []
    self.addr = []
    self.data_page_id = "Data page ID"
    self.rs1_reg = "Register source 1"
    self.reserved_destinations = []
    self.avail_regs = [
    ]  # User can specify a small group of available registers to generate various
    # hazard condition. TO DO: enable this later
    self.solution = "A random solution which meets given constraints"
    self.problem_num_load_store = constraint.Problem(
        constraint.MinConflictsSolver())
    self.problem = constraint.Problem(constraint.MinConflictsSolver())

  def problem_definition(self):
    # This line is for when we had num_load_store as a random.randint value
    # self.num_load_store = random.randint(0, 32)
    # Note that we can not add num_load_store to the original problem, as we
    # need the result to be used in the original problem
    # We might have already added num_load_store to the problem_num_load_store
    # in the child classes, if not, add it here
    if self.num_load_store not in self.problem_num_load_store._variables:
      self.problem_num_load_store.addVariable(self.num_load_store, range(32))
    # self.offset = range(self.num_load_store)
    rand_val = self.problem_num_load_store.getSolution()[self.num_load_store]
    self.offset = range(rand_val)

    # Error: ValueError: Tried to insert duplicated variable 0
    # self.addr = range(self.num_load_store)
    # self.addr = range(self.num_load_store, 2*self.num_load_store)
    self.addr = range(rand_val, 2 * rand_val)

    # I get memory error for the below line!
    # self.problem.addVariables(self.offset, range(-32768, 32768))
    self.problem.addVariables(self.offset, range(-32, 32))
    # self.problem.addVariables(self.addr, range(-32768, 32768))
    self.problem.addVariables(self.addr, range(-32, 32))

    self.problem.addVariable(self.num_mixed_instr, range(0, 30))
    self.problem.addVariable(self.rs1_reg, utils.riscv_reg_t)
    # self.problem.addVariable(self.base, range(-32768, 32768))
    self.problem.addVariable(self.base, range(-32, 32))
    # self.problem.addVariable(self.data_page_id, range(65536))
    self.problem.addVariable(self.data_page_id, range(128))

    # TO DO: addVariable avai_regs

    # size_constraint has been already applied as the size of offset and addr is num_load_store
    def size_c(offset, addr, num_load_store):
      if len(offset) == num_load_store and len(addr) == num_load_store:
        return True

    def rs1_c(rs1_reg):
      # TO DO: cfg
      if rs1_reg not in [self.reserved_destinations, "ZERO"]:
        return True

    def addr_c(data_page_id, base, offset, addr):
      cond1 = data_page_id < self.max_data_page_id
      cond2 = base in range(self.max_load_store_offset)
      if addr == base + offset and addr in range(
          self.max_load_store_offset) and offset in range(
              -2048, 2048) and cond1 and cond2:
        return True

    self.problem.addConstraint(rs1_c, [self.rs1_reg])
    for i in self.offset:
      self.problem.addConstraint(
          addr_c, [self.data_page_id, self.base, i, rand_val + i])

  def post_randomize(self):
    self.gen_load_store_instr()
    # rs1 cannot be modified by other instructions
    if self.solution[self.rs1_reg] not in self.reserved_destinations:
      self.reserved_destinations.append(self.solution[self.rs1_reg])
    self.add_mixed_instr()
    self.add_rs1_init_la_instr()
    super().post_randomize()

  def la_rd_c(self, instr):
    # instr.problem.addVariable(self.rs1_reg, utils.riscv_reg_t)
    def la_rd_c(destination):
      if destination == self.solution[self.rs1_reg]:
        return True

    # instr.problem.addConstraint(la_rd_c, [instr.instr_rd, self.rs1_reg])
    instr.problem.addConstraint(la_rd_c, [instr.instr_rd])

  # Use "la" instruction to initialize the base register: Need attention!
  def add_rs1_init_la_instr(self):
    la_instr = riscv_instr_base.riscv_pseudo_instr()
    # la_instr.problem_definition(lambda: la_rd_c(self.instr_rd, self.rs1_reg), la_instr=1)
    la_instr.problem_definition(la_instr=1)
    # Adding the new constraint (rd==rs1_reg)
    self.la_rd_c(la_instr)
    # Now we can randomize it (get a solution as we applied all the needed constraints)
    la_instr.randomize()
    # print("TODO: la randomized!!")
    if self.access_u_mode_mem:
      la_instr.imm_str = "data_page_{}+{}".format(
          self.solution[self.data_page_id], self.solution[self.base])
    else:
      la_instr.imm_str = "kernel_data_page_{}+{}".format(
          self.solution[self.data_page_id], self.solution[self.base])
    self.instr_list.insert(0, la_instr)

  def gen_load_store_instr_c(self, instr):
    # Comment for now as we don't need to add new var to the instr
    # instr.problem.addVariable(self.rs1_reg, utils.riscv_reg_t)
    # TO DO: add avail_regs
    # instr.problem.addVariable(self., utils.riscv_reg_t)

    # def rs1_c(rs1, rs1_reg):
    #     if rs1 == rs1_reg:
    #         return True

    def rs1_c(rs1):
      if rs1 == self.solution[self.rs1_reg]:
        return True

    def instr_name_c(name):
      if name in self.allowed_instr:
        return True

    def rd_c(rd, avail_reg):
      if len(avail_reg) > 0:
        if rd in avail_reg:
          return True
      else:
        return True

    def rd_rs1_c(rd, rs1):
      if rd != rs1:
        return True

    # instr.problem.addConstraint(rs1_c, [instr.instr_src1, self.rs1_reg])
    instr.problem.addConstraint(rs1_c, [instr.instr_src1])
    instr.problem.addConstraint(instr_name_c, [instr.instr_name])
    # TO DO: enable later
    # instr.problem.addConstraint(rd_c, [instr.instr_rd, self.avail_regs])
    instr.problem.addConstraint(rd_rs1_c, [instr.instr_rd, instr.instr_src1])

  # Generate each load/store instruction
  def gen_load_store_instr(self):
    enable_compressed_load_store = 0
    self.allowed_instr = []
    # TO DO: enabling compressed_load_store
    # if self.solution[self.rs1_reg] in S0_to_A5:
    #     enable_compressed_load_store = 1

    if len(self.avail_regs) > 0:
      pass
      # randomize the avail_regs
      # for i in range(len(self.avail_regs)):
      #     self.avail_regs[i] = random.choice(utils.riscv_reg_t)
    for i in range(len(self.addr)):
      rand_instr = riscv_rand_instr.riscv_rand_instr()
      # TO DO: cfg
      # rand_instr.cfg = cfg
      rand_instr.reserved_rd = self.reserved_destinations
      # Assign the allowed load/store instructions based on address alignment
      # This is done separately rather than a constraint to improve the randomization performance
      self.allowed_instr = ["LB", "LBU", "SB"]
      if self.solution[self.addr[i]] % 2 == 0:
        self.allowed_instr = ["LH", "LHU", "SH"] + self.allowed_instr
      if self.solution[self.addr[i]] % 4 == 0:
        self.allowed_instr = ["LW", "SW", "LWU"] + self.allowed_instr
        if self.solution[self.offset[i]] in range(
            128) and self.solution[self.offset[i]] % 4 == 0:
          self.allowed_instr = ["C_LW", "C_SW"] + self.allowed_instr
      if self.solution[self.addr[i]] % 8 == 0:
        self.allowed_instr = ["LD", "SD"] + self.allowed_instr
        if self.solution[self.offset[i]] in range(
            256) and self.solution[self.offset[i]] % 8 == 0:
          self.allowed_instr = ["C_LD", "C_SD"] + self.allowed_instr
      # Now it's time to randomize rand_instr
      rand_instr.problem_definition(no_load_store=0)
      self.gen_load_store_instr_c(rand_instr)
      rand_instr.randomize()

      rand_instr.process_load_store = 0
      rand_instr.imm_str = "{}".format(self.solution[self.offset[i]])
      self.instr_list.append(rand_instr)

  def add_mixed_instr_c(self, instr):
    # TO DO: add_variable for avail_regs to the instr
    #instr.problem.add_variable...
    def rs1_rd_c(rs1, rd, avail_regs):
      if len(avail_regs) > 0:
        if rs1 in avail_regs and rd in avail_regs:
          return True
      else:
        return True

    def category_c(category):
      if category not in ["LOAD", "STORE", "BRANCH", "JUMP"]:
        return True

    # TO DO: call addConstraint for rs1_rd_c
    instr.problem.addConstraint(category_c, [instr.instr_category])

  # Insert some other instructions to mix with load/store instruction

  def add_mixed_instr(self):
    for i in range(self.solution[self.num_mixed_instr]):
      rand_instr = riscv_rand_instr.riscv_rand_instr()
      # TO DO: cfg
      # rand_instr.cfg = self.cfg
      rand_instr.reserved_rd = self.reserved_destinations
      # randomizing the rand_instr
      rand_instr.problem_definition()
      # additional constraints
      self.add_mixed_instr_c(rand_instr)
      rand_instr.randomize()
      self.insert_instr(rand_instr)

  def randomize(self):
    self.solution = self.problem.getSolution()
    self.post_randomize()


# A single load/store instruction
class riscv_single_load_store_instr_stream(riscv_load_store_base_instr_stream):

  def problem_definition(self):
    # legal_c constraint for problem_num_load_store
    def legal_c_problem_num_load_store(num_load_store):
      if num_load_store == 1:
        return True

    # legal_c constraint for problem
    def legal_c_problem(num_mixed_instr):
      if num_mixed_instr < 5:
        return True

    if self.num_load_store not in self.problem_num_load_store._variables:
      self.problem_num_load_store.addVariable(self.num_load_store, range(32))
    # applying the constraint, before calling the super().problem_definition
    # (because we get the solution in there
    self.problem_num_load_store.addConstraint(legal_c_problem_num_load_store,
                                              [self.num_load_store])
    # Calling the super problem_definition, to apply all the constraints to the base object
    super().problem_definition()

    self.problem.addConstraint(legal_c_problem, [self.num_mixed_instr])


# Back to back load/store instructions
class riscv_load_store_stress_instr_stream(riscv_load_store_base_instr_stream):
  max_instr_cnt = 30
  min_instr_cnt = 10

  def problem_definition(self):
    # legal_c constraint for problem_num_load_store
    def legal_c_problem_num_load_store(num_load_store):
      if num_load_store <= max_instr_cnt and num_load_store >= min_instr_cnt:
        return True

    # legal_c constraint for problem
    def legal_c_problem(num_mixed_instr):
      if num_mixed_instr == 0:
        return True

    if self.num_load_store not in self.problem_num_load_store._variables:
      self.problem_num_load_store.addVariable(self.num_load_store, range(32))
    # applying the constraint, before calling the super().problem_definition
    # (because we get the solution in there
    self.problem_num_load_store.addConstraint(legal_c_problem_num_load_store,
                                              [self.num_load_store])
    # Calling the super problem_definition, to apply all the constraints to the base object
    super().problem_definition()

    self.problem.addConstraint(legal_c_problem, [self.num_mixed_instr])


class riscv_load_store_rand_instr_stream(riscv_load_store_base_instr_stream):

  def problem_definition(self):
    # legal_c constraint for problem_num_load_store
    def legal_c_problem_num_load_store(num_load_store):
      if num_load_store in range(10, 31):
        return True

    # legal_c constraint for problem
    def legal_c_problem(num_mixed_instr):
      if num_mixed_instr in range(10, 31):
        return True

    # def legal_c_problem(num_load_store, num_mixed_instr):
    #     if num_load_store in range(10, 31) and num_mixed_instr in range(10, 31):
    #         return True

    if self.num_load_store not in self.problem_num_load_store._variables:
      self.problem_num_load_store.addVariable(self.num_load_store, range(32))
    # applying the constraint, before calling the super().problem_definition
    # (because we get the solution in there
    self.problem_num_load_store.addConstraint(legal_c_problem_num_load_store,
                                              [self.num_load_store])
    # Calling the super problem_definition, to apply all the constraints to the base object
    super().problem_definition()

    self.problem.addConstraint(legal_c_problem, [self.num_mixed_instr])


# Use a small set of GPR to create various WAW, RAW, WAR hazard scenario
class riscv_hazard_instr_stream(riscv_load_store_base_instr_stream):
  num_of_avail_regs = 6

  def problem_definition(self):
    # legal_c constraint for problem_num_load_store
    def legal_c_problem_num_load_store(num_load_store):
      if num_load_store in range(10, 31):
        return True

    # legal_c constraint for problem
    def legal_c_problem(num_mixed_instr):
      if num_mixed_instr in range(10, 31):
        return True

    if self.num_load_store not in self.problem_num_load_store._variables:
      self.problem_num_load_store.addVariable(self.num_load_store, range(32))
    # applying the constraint, before calling the super().problem_definition (because we get the solution in there
    self.problem_num_load_store.addConstraint(legal_c_problem_num_load_store,
                                              [self.num_load_store])
    # Calling the super problem_definition, to apply all the constraints to the base object
    super().problem_definition()

    self.problem.addConstraint(legal_c_problem, [self.num_mixed_instr])

  def pre_randomize(self):
    self.avail_regs = [None] * num_of_avail_regs
    super().pre_randomize()
