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

import random
import constraint


#------------------------------------------------------------------------------
# RISC-V abstract program class
#
# This class is used to model a node in a callstack tree, no actual instruction
# is included in this class.
#------------------------------------------------------------------------------
class riscv_program:

  def __init__(self, name):
    self.name = name
    self.program_id = "ID of the current program"
    self.call_stack_level = ("The level of current program in the call stack "
                             "tree")
    self.sub_program_id = [
    ]  # The list of all sub-programs of the current program
    self.solution = "A random solution which meets given constraints"
    self.problem = constraint.Problem(constraint.MinConflictsSolver())

  def problem_definition(self):
    # TO DO: change the ranges (small ranges for now)
    # List of sub_program_ids, to randomize unique ids
    self.sub_program_id_list = []
    self.num_of_sub_programs = random.randint(0, 20)
    self.sub_program_id = range(self.num_of_sub_programs)
    self.problem.addVariables(self.sub_program_id, range(25))
    self.problem.addVariable(self.program_id, range(50))

    def legal_c(sub_prog_id, prog_id):
      cond1 = sub_prog_id not in self.sub_program_id_list
      cond2 = sub_prog_id != prog_id
      if cond1 and cond2:
        self.sub_program_id_list.append(sub_prog_id)
        return True

    for i in self.sub_program_id:
      self.problem.addConstraint(legal_c, [i, self.program_id])

  def convert2string(self):
    str = "PID[{}] Lv[{}] :".format(self.solution[self.program_id],
                                    self.call_stack_level)
    for item in self.sub_program_id:
      str = "{} {}".format(str, item)
    return str

  def randomize(self):
    self.solution = self.problem.getSolution()


#-----------------------------------------------------------------------------------------
# RISC-V assembly program call stack generator
#
# The call stack is generated as a tree structure to avoid dead call loop.
# Level 0:                     P0
#                           /  |  \
# Level 1:                 P1  P2  P3
#                          |     \/  \
# Level 2:                 P4    P5   P6
#                                 |
# Level 3:                        P7
#
# Rules: A program can only call the program in the next level.
#        A program can be called many times by other upper level programs.
#        A program can call the same lower level programs multiple times.
#-----------------------------------------------------------------------------------------
class riscv_callstack_gen:

  def __init__(self, name):
    self.name = name
    # Number of programs in the call stack
    self.program_cnt = 10
    # Handles of all programs
    self.program_h = []  # objects are from type "riscv_program"
    # Maximum call stack level
    self.max_stack_level = 50
    # Call stack level of each program
    self.stack_level = []
    self.solution = "A random solution which meets given constraints"
    self.problem = constraint.Problem(constraint.MinConflictsSolver())

  def problem_definition(self):
    self.stack_level = range(self.program_cnt)
    self.problem.addVariable(self.stack_level[0], [0])
    self.problem.addVariables(self.stack_level[1:], range(1, self.program_cnt))

    def program_stack_level_c(level, level_minus_one):
      # Already applied
      # cond1 = level in range(1, self.program_cnt)
      if level_minus_one <= level <= level_minus_one + 1 and level <= self.max_stack_level:
        return True

    for i in self.stack_level[1:]:
      self.problem.addConstraint(program_stack_level_c, [i, i - 1])

  # Init all program instances before randomization
  def init(self, program_cnt):
    self.program_cnt = program_cnt
    self.program_h = [None] * program_cnt
    for i in range(len(self.program_h)):
      self.program_h[i] = riscv_program("program_{}".format(i))

  def randomize(self):
    solution_existed = 0
    self.solution = self.problem.getSolution()
    self.post_randomize()
    if self.solution:
      solution_existed = 1
    return solution_existed

  # In the randomiation stage, only the stack level of each program is specified. The call stack
  # generation process is to build the call relationship between different programs. This is
  # implemented with post randomize rather than constraints for performance considerations.
  # Solving a complex call stack with SV constraint could take considerable time for the solver.
  def post_randomize(self):
    last_level = self.stack_level[self.program_cnt - 1]
    for i in range(len(self.program_h)):
      self.program_h[i].program_id = i
      self.program_h[i].call_stack_level = self.stack_level[i]

    # Top-down generate the entire call stack.
    # A program can only call the programs in the next level.
    for i in range(last_level):
      program_list = []
      next_program_list = []
      idx = 0
      # sub_program_id_pool = []
      # sub_program_cnt = []
      for j in range(len(self.stack_level)):
        if self.stack_level[j] == i:
          program_list.append(j)
        if self.stack_level[j] == i + 1:
          next_program_list.append(j)

      # Randomly duplicate some sub programs in the pool to create a case that
      # one sub program is called by multiple caller. Also it's possible to call
      # the same sub program in one program multiple times.
      total_sub_program_cnt = random.randint(
          len(next_program_list),
          len(next_program_list) + 1)
      sub_program_id_pool = [None] * total_sub_program_cnt
      for j in range(len(sub_program_id_pool)):
        if j < len(next_program_list):
          sub_program_id_pool[j] = next_program_list[j]
        else:
          sub_program_id_pool[j] = random.choice(next_program_list)

      random.shuffle(sub_program_id_pool)
      sub_program_cnt = [None] * len(program_list)
      for i in range(len(program_list)):
        sub_program_cnt[i] = i
      # Distribute the programs of the next level among the programs of current level
      # Make sure all program has a caller so that no program is obsolete.
      problem = constraint.Problem(constraint.MinConflictsSolver())
      problem.addVariables(sub_program_cnt,
                           range(0,
                                 len(sub_program_id_pool) + 1))
      problem.addConstraint(
          constraint.ExactSumConstraint(len(sub_program_id_pool)),
          [item for item in sub_program_cnt])
      solution = problem.getSolution()
      for j in range(len(program_list)):
        id = program_list[j]
        self.program_h[id].sub_program_id = [None
                                            ] * solution[sub_program_cnt[j]]
        for i in range(len(self.program_h[id].sub_program_id)):
          self.program_h[id].sub_program_id[i] = sub_program_id_pool[idx]
          idx += 1

  def print_call_stack(self, id, str):
    if len(self.program_h[id].sub_program_id) == 0:
      print(str)
    else:
      for item in self.program_h[id].sub_program_id:
        print_call_stack(item, "{} -> {}".format(str, item))
