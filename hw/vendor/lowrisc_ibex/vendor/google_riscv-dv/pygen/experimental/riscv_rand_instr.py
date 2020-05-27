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
import utils


class riscv_rand_instr(riscv_instr_base.riscv_instr_base):

  def __init__(self):
    # Calling the super constructor
    riscv_instr_base.riscv_instr_base.__init__(self)
    # TODO: TO DO config
    # Some additional reserved registers
    self.reserved_rd = []

  def problem_definition(self,
                         no_branch=0,
                         no_load_store=1,
                         enable_hint_instr=0):
    # Calling the super problem_definition, to apply all the constraints to the base object
    super().problem_definition(no_branch, no_load_store, enable_hint_instr)

    # TO DO: need to complete it when we support compressed instructions
    def instr_c(category, rd, rs1):
      cond1 = category in [
          "LOAD", "STORE", "SHIFT", "ARITHMETIC", "LOGICAL", "BRANCH",
          "COMPARE", "CSR", "SYSTEM", "SYNCH"
      ]
      cond2 = rs1 not in [self.reserved_rd, "ZERO"
                         ] if category in ["LOAD", "STORE"] else True
      cond3 = rd not in self.reserved_rd if len(self.reserved_rd) > 0 else True
      # TO DO: Compressed instruction may use the same CSR for both rs1 and rd
      if cond1 and cond2 and cond3:
        return True

    # TO DO: Registers specified by the three-bit rs1’, rs2’, and rd’ fields of the CIW, CL, CS,
    # and CB formats
    def rvc_csr_c():
      pass

    def constraint_cfg_knob_c(name):
      # TO DO: cfg for no_ebreak, no_wfi, no_load_store, and no_branch_jump
      if name not in ["ECALL", "URET", "SRET", "MRET"]:
        return True

    self.problem.addConstraint(
        instr_c, [self.instr_category, self.instr_rd, self.instr_src1])
    self.problem.addConstraint(constraint_cfg_knob_c, [self.instr_name])
    return
