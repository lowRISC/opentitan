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

import traceback
from pygen_src.isa.riscv_cov_instr import *


class riscv_instr_cover_group:
    def __init__(self):
        self.pre_instr = riscv_cov_instr()
        self.cfg = None
        self.instr_list = []
        self.instr_cnt = 0
        self.branch_instr_cnt = 0
        self.branch_hit_history = vsc.bit_t(5)  # The last 5 branch result
        self.ignored_exceptions = []
        self.exception_list = []
        ''' 
        Mode of the coverage model:
        In compliance mode, all the micro-architecture related covergroups 
        are removed. Only the ones related to RISC-V specification compliance
        is sampled.
        '''
        self.compliance_mode = vsc.bit_t(1)
        self.select_isa = vsc.bit_t(1)  # Select an ISA extension to cover
        self.cov_isa = None
        self.cg_instantiation()

    '''Format specific covergroups'''

    @vsc.covergroup
    class r_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class i_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class u_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class cmp_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_result = vsc.coverpoint(lambda: self.instr.rd_value[0],
                                            bins={
                                                "Unset": vsc.bin(0),
                                                "Set"  : vsc.bin(1)
                                            }
                                            )
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class sb_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_branch_hit = vsc.coverpoint(lambda: self.instr.branch_hit,
                                                bins={
                                                    "Taken"    : vsc.bin(1),
                                                    "Non-taken": vsc.bin(0)
                                                }
                                                )
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    @vsc.covergroup
    class j_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            '''The RISC-V hardware allows any of the 32 integer registers 
            to be given as rd. If register 0 (ZERO) is given as rd then the 
            return address is discarded and we effectively have a
            goto rather than a function call'''
            # if instr.rd:
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd_align = vsc.coverpoint(lambda: self.instr.rd_value[1],
                                              bins={
                                                  "Aligned"    : vsc.bin(1),
                                                  "Not-aligned": vsc.bin(0)
                                              }
                                              )

    ''' RV64M instruction '''
    # Below instructions only do calculation based on lower 32 bits, and extend the result to 64
    # bits. Add special covergroup for corner cases

    @vsc.covergroup
    class mulw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign])

    @vsc.covergroup
    class divw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])

    @vsc.covergroup
    class divuw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])

    @vsc.covergroup
    class remw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign])

    @vsc.covergroup
    class remuw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign])


    ''' RV64C instruction'''

    @vsc.covergroup
    class c_ld_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))

    @vsc.covergroup
    class c_ldsp_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(compressed_gpr))

    @vsc.covergroup
    class c_sd_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class c_sdsp_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                        cp_t=vsc.enum_t(compressed_gpr))

    @vsc.covergroup
    class c_addiw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class c_subw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class c_addw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    ''' RV64I Instruction '''

    @vsc.covergroup
    class lwu_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))

    @vsc.covergroup
    class ld_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))

    @vsc.covergroup
    class sd_cg(object):
         def __init__(self):
             super().__init__()
             self.instr = None
             self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                          cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
             self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                          cp_t=vsc.enum_t(riscv_reg_t))
             self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                               cp_t=vsc.enum_t(operand_sign_e))
             self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                 cp_t=vsc.enum_t(branch_hazard_e))
             self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                 cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class sraw_cg(object):
         def __init__(self):
             super().__init__()
             self.instr = None
             self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                          cp_t=vsc.enum_t(riscv_reg_t))
             self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                          cp_t=vsc.enum_t(riscv_reg_t))
             self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                         cp_t=vsc.enum_t(riscv_reg_t))
             self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                               cp_t=vsc.enum_t(operand_sign_e))
             self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                               cp_t=vsc.enum_t(operand_sign_e))
             self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
             self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                 cp_t=vsc.enum_t(hazard_e))
             self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                         self.cp_rd_sign])

    @vsc.covergroup
    class sllw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                        self.cp_rd_sign])

    @vsc.covergroup
    class srlw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign])

    '''' // imm[5] could be 1 for RV64I SLLI/SRAI/SRLI'''

    @vsc.covergroup
    class srai64_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class slli64_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class srli64_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class sraiw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class slliw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))


    @vsc.covergroup
    class srliw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))


    @vsc.covergroup
    class addw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                        self.cp_rd_sign])

    @vsc.covergroup
    class subw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                           self.cp_rd_sign])

    @vsc.covergroup
    class addiw_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_logical = vsc.coverpoint(lambda: self.instr.logical_similarity,
                                             cp_t=vsc.enum_t(logical_similarity_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_imm_sign])


    '''Category specific covergroups'''
    '''Load instructions'''
    @vsc.covergroup
    class load_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    '''TODO: covergroup inheritance is broken at the moment. The workaround 
    will be switched back to the inheritance approach once it gets fixed'''

    # @vsc.covergroup
    # class lb_cg(load_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class lb_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    # @vsc.covergroup
    # class lh_cg(load_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_align = vsc.coverpoint(lambda: instr.unaligned_mem_access,
    #                                        bins={
    #                                            "aligned"  : vsc.bin(0),
    #                                            "unaligned": vsc.bin(1)
    #                                        })
    @vsc.covergroup
    class lh_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_align = vsc.coverpoint(lambda: self.instr.unaligned_mem_access,
                                           bins={
                                               "aligned"  : vsc.bin(0),
                                               "unaligned": vsc.bin(1)
                                           })

    # @vsc.covergroup
    # class lw_cg(load_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_align = vsc.coverpoint(lambda: instr.unaligned_mem_access,
    #                                        bins={
    #                                            "aligned"  : vsc.bin(0),
    #                                            "unaligned": vsc.bin(1)
    #                                        })
    @vsc.covergroup
    class lw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

            self.cp_align = vsc.coverpoint(lambda: self.instr.unaligned_mem_access,
                                           bins={
                                               "aligned"  : vsc.bin(0),
                                               "unaligned": vsc.bin(1)
                                           })

    # @vsc.covergroup
    # class lbu_cg(load_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class lbu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    # @vsc.covergroup
    # class lhu_cg(load_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_align = vsc.coverpoint(lambda: instr.unaligned_mem_access,
    #                                        bins={
    #                                            "aligned"  : vsc.bin(0),
    #                                            "unaligned": vsc.bin(1)
    #                                        })
    @vsc.covergroup
    class lhu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_align = vsc.coverpoint(lambda: self.instr.unaligned_mem_access,
                                           bins={
                                               "aligned"  : vsc.bin(0),
                                               "unaligned": vsc.bin(1)
                                           })

    '''Store instructions'''

    @vsc.covergroup
    class store_instr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    store_lsu_hazard_e))

    # @vsc.covergroup
    # class sb_cg(store_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class sb_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    store_lsu_hazard_e))

    # @vsc.covergroup
    # class sh_cg(store_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_misalign = vsc.coverpoint(
    #             lambda: instr.unaligned_mem_access,
    #             bins={
    #                 "aligned"  : vsc.bin(0),
    #                 "unaligned": vsc.bin(1)
    #             })
    @vsc.covergroup
    class sh_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    store_lsu_hazard_e))
            self.cp_misalign = vsc.coverpoint(
                lambda: self.instr.unaligned_mem_access,
                bins={
                    "aligned"  : vsc.bin(0),
                    "unaligned": vsc.bin(1)
                })

    # @vsc.covergroup
    # class sw_cg(store_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_misalign = vsc.coverpoint(
    #             lambda: instr.unaligned_mem_access,
    #             bins={
    #                 "aligned"  : vsc.bin(0),
    #                 "unaligned": vsc.bin(1)
    #             })
    @vsc.covergroup
    class sw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    store_lsu_hazard_e))
            self.cp_misalign = vsc.coverpoint(
                lambda: self.instr.unaligned_mem_access,
                bins={
                    "aligned"  : vsc.bin(0),
                    "unaligned": vsc.bin(1)
                })

    '''Shift instructions'''

    # @vsc.covergroup
    # class sll_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class sll_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    @vsc.covergroup
    class slli_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    # @vsc.covergroup
    # class srl_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class srl_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    @vsc.covergroup
    class srli_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    # @vsc.covergroup
    # class sra_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class sra_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    @vsc.covergroup
    class srai_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    '''Arithmetic instructions'''

    # @vsc.covergroup
    # class add_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
    #                                         self.cp_rd_sign])
    @vsc.covergroup
    class add_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])

    @vsc.covergroup
    class addi_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_imm_sign,
                                            self.cp_rd_sign])

    # @vsc.covergroup
    # class sub_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
    #                                         self.cp_rd_sign])
    @vsc.covergroup
    class sub_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])

    # @vsc.covergroup
    # class lui_cg(u_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class lui_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    # @vsc.covergroup
    # class auipc_cg(u_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class auipc_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    '''Logical instructions'''

    # @vsc.covergroup
    # class xor_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_logical = vsc.coverpoint(lambda: instr.logical_similarity,
    #                                          cp_t=vsc.enum_t(
    #                                              logical_similarity_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class xor_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_logical = vsc.coverpoint(lambda: self.instr.logical_similarity,
                                             cp_t=vsc.enum_t(
                                                 logical_similarity_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    # @vsc.covergroup
    # class xori_cg(i_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_logical = vsc.coverpoint(lambda: instr.logical_similarity,
    #                                          cp_t=vsc.enum_t(
    #                                              logical_similarity_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_imm_sign])
    @vsc.covergroup
    class xori_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_logical = vsc.coverpoint(lambda: self.instr.logical_similarity,
                                             cp_t=vsc.enum_t(
                                                 logical_similarity_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_imm_sign])

    # @vsc.covergroup
    # class or_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_logical = vsc.coverpoint(lambda: instr.logical_similarity,
    #                                          cp_t=vsc.enum_t(
    #                                              logical_similarity_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class or_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_logical = vsc.coverpoint(lambda: self.instr.logical_similarity,
                                             cp_t=vsc.enum_t(
                                                 logical_similarity_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    # @vsc.covergroup
    # class ori_cg(i_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_logical = vsc.coverpoint(lambda: instr.logical_similarity,
    #                                          cp_t=vsc.enum_t(
    #                                              logical_similarity_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_imm_sign])
    @vsc.covergroup
    class ori_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_logical = vsc.coverpoint(lambda: self.instr.logical_similarity,
                                             cp_t=vsc.enum_t(
                                                 logical_similarity_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_imm_sign])

    # @vsc.covergroup
    # class and_cg(r_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_logical = vsc.coverpoint(lambda: instr.logical_similarity,
    #                                          cp_t=vsc.enum_t(
    #                                              logical_similarity_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class and_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_logical = vsc.coverpoint(lambda: self.instr.logical_similarity,
                                             cp_t=vsc.enum_t(
                                                 logical_similarity_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    # @vsc.covergroup
    # class andi_cg(i_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_logical = vsc.coverpoint(lambda: instr.logical_similarity,
    #                                          cp_t=vsc.enum_t(
    #                                              logical_similarity_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_imm_sign])
    @vsc.covergroup
    class andi_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_logical = vsc.coverpoint(lambda: self.instr.logical_similarity,
                                             cp_t=vsc.enum_t(
                                                 logical_similarity_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_imm_sign])

    '''Compare instructions'''

    # @vsc.covergroup
    # class slt_cg(cmp_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_rs2 = vsc.coverpoint(lambda: instr.rs2,
    #                                      cp_t=vsc.enum_t(riscv_reg_t))
    #         self.cp_rs2_sign = vsc.coverpoint(lambda: instr.rs2_sign,
    #                                           cp_t=vsc.enum_t(operand_sign_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class slt_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_result = vsc.coverpoint(lambda: self.instr.rd_value[0],
                                            bins={
                                                "Unset": vsc.bin(0),
                                                "Set"  : vsc.bin(1)
                                            }
                                            )
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    # @vsc.covergroup
    # class slti_cg(cmp_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_imm_sign = vsc.coverpoint(lambda: instr.imm_sign,
    #                                           cp_t=vsc.enum_t(operand_sign_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_imm_sign])
    @vsc.covergroup
    class slti_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_result = vsc.coverpoint(lambda: self.instr.rd_value[0],
                                            bins={
                                                "Unset": vsc.bin(0),
                                                "Set"  : vsc.bin(1)
                                            }
                                            )
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_imm_sign])

    # @vsc.covergroup
    # class sltu_cg(cmp_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_rs2 = vsc.coverpoint(lambda: instr.rs2,
    #                                      cp_t=vsc.enum_t(riscv_reg_t))
    #         self.cp_rs2_sign = vsc.coverpoint(lambda: instr.rs2_sign,
    #                                           cp_t=vsc.enum_t(operand_sign_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_rs2_sign])
    @vsc.covergroup
    class sltu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_result = vsc.coverpoint(lambda: self.instr.rd_value[0],
                                            bins={
                                                "Unset": vsc.bin(0),
                                                "Set"  : vsc.bin(1)
                                            }
                                            )
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])

    # @vsc.covergroup
    # class sltiu_cg(cmp_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_imm_sign = vsc.coverpoint(lambda: instr.imm_sign,
    #                                           cp_t=vsc.enum_t(operand_sign_e))
    #         self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
    #                                         self.cp_imm_sign])
    @vsc.covergroup
    class sltiu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_result = vsc.coverpoint(lambda: self.instr.rd_value[0],
                                            bins={
                                                "Unset": vsc.bin(0),
                                                "Set"  : vsc.bin(1)
                                            }
                                            )
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_imm_sign])

    '''Branch instructions'''

    # @vsc.covergroup
    # class beq_cg(sb_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class beq_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_branch_hit = vsc.coverpoint(lambda: self.instr.branch_hit,
                                                bins={
                                                    "Non-taken": vsc.bin(0),
                                                    "Taken"    : vsc.bin(1),
                                                }
                                                )
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    # @vsc.covergroup
    # class bne_cg(sb_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class bne_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_branch_hit = vsc.coverpoint(lambda: self.instr.branch_hit,
                                                bins={
                                                    "Taken"    : vsc.bin(1),
                                                    "Non-taken": vsc.bin(0)
                                                }
                                                )
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    # @vsc.covergroup
    # class blt_cg(sb_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class blt_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_branch_hit = vsc.coverpoint(lambda: self.instr.branch_hit,
                                                bins={
                                                    "Taken"    : vsc.bin(1),
                                                    "Non-taken": vsc.bin(0)
                                                }
                                                )
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    # @vsc.covergroup
    # class bge_cg(sb_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class bge_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_branch_hit = vsc.coverpoint(lambda: self.instr.branch_hit,
                                                bins={
                                                    "Taken"    : vsc.bin(1),
                                                    "Non-taken": vsc.bin(0)
                                                }
                                                )
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    # @vsc.covergroup
    # class bltu_cg(sb_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class bltu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_branch_hit = vsc.coverpoint(lambda: self.instr.branch_hit,
                                                bins={
                                                    "Taken"    : vsc.bin(1),
                                                    "Non-taken": vsc.bin(0)
                                                }
                                                )
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    # @vsc.covergroup
    # class bgeu_cg(sb_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    @vsc.covergroup
    class bgeu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_branch_hit = vsc.coverpoint(lambda: self.instr.branch_hit,
                                                bins={
                                                    "Taken"    : vsc.bin(1),
                                                    "Non-taken": vsc.bin(0)
                                                }
                                                )
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign,
                                            self.cp_rs2_sign])
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))

    '''Jump instructions'''

    # @vsc.covergroup
    # class jal_cg(j_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         self.cp_imm_align = vsc.coverpoint(lambda: instr.imm[1],
    #                                            bins={
    #                                                "Aligned"    : vsc.bin(1),
    #                                                "Not-aligned": vsc.bin(0)
    #                                            }
    #                                            )
    @vsc.covergroup
    class jal_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            '''The RISC-V hardware allows any of the 32 integer registers 
            to be given as rd. If register 0 (ZERO) is given as rd then the 
            return address is discarded and we effectively have a
            goto rather than a function call'''
            # if self.instr.rd:
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd_align = vsc.coverpoint(lambda: self.instr.rd_value[1],
                                              bins={
                                                  "Aligned"    : vsc.bin(1),
                                                  "Not-aligned": vsc.bin(0)
                                              }
                                              )
            self.cp_imm_align = vsc.coverpoint(lambda: self.instr.imm[1],
                                               bins={
                                                   "Aligned"    : vsc.bin(1),
                                                   "Not-aligned": vsc.bin(0)
                                               }
                                               )

    # @vsc.covergroup
    # class jalr_cg(j_instr_cg):
    #     def __init__(self, instr):
    #         super().__init__(instr)
    #
    #         '''default bins are not supported in pyvsc. We ignore it here
    #         as coverage values hit in default bin are not taken account while
    #         reporting coverage'''
    #         self.cp_rs1_link = vsc.coverpoint(lambda: instr.rs1,
    #                                           cp_t=vsc.enum_t(
    #                                               jalr_riscv_reg_t))
    #         self.cp_rd_link = vsc.coverpoint(lambda: instr.rd,
    #                                          cp_t=vsc.enum_t(jalr_riscv_reg_t))
    #         # left index is excluded in pyvsc bit_t type
    #         self.cp_imm_align = vsc.coverpoint(lambda: instr.imm[2:0],
    #                                            bins={
    #                                                "Zero" : vsc.bin(0),
    #                                                "One"  : vsc.bin(1),
    #                                                "Two"  : vsc.bin(2),
    #                                                "Three": vsc.bin(3)
    #                                            }
    #                                            )
    #         self.cp_rs1_align = vsc.coverpoint(lambda: instr.rs1_value[2:0],
    #                                            bins={
    #                                                "Zero" : vsc.bin(0),
    #                                                "One"  : vsc.bin(1),
    #                                                "Two"  : vsc.bin(2),
    #                                                "Three": vsc.bin(3)
    #                                            }
    #                                            )
    #         self.cp_align = vsc.cross([self.cp_imm_align, self.cp_rs1_align])
    #         self.cp_ras = vsc.cross([self.cp_rs1_link, self.cp_rd_link])
    @vsc.covergroup
    class jalr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            '''The RISC-V hardware allows any of the 32 integer registers 
            to be given as rd. If register 0 (ZERO) is given as rd then the 
            return address is discarded and we effectively have a
            goto rather than a function call'''
            # TODO: if self.instr.rd:
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd_align = vsc.coverpoint(lambda: self.instr.rd_value[1],
                                              bins={
                                                  "Aligned"    : vsc.bin(1),
                                                  "Not-aligned": vsc.bin(0)
                                              }
                                              )
            '''default bins are not supported in pyvsc. We ignore it here 
            as coverage values hit in default bin are not taken account while 
            reporting coverage'''
            self.cp_rs1_link = vsc.coverpoint(lambda: self.instr.rs1,
                                              cp_t=vsc.enum_t(
                                                  jalr_riscv_reg_t))
            self.cp_rd_link = vsc.coverpoint(lambda: self.instr.rd,
                                             cp_t=vsc.enum_t(jalr_riscv_reg_t))
            # left index is excluded in pyvsc bit_t type
            self.cp_imm_align = vsc.coverpoint(lambda: self.instr.imm[2:0],
                                               bins={
                                                   "Zero" : vsc.bin(0),
                                                   "One"  : vsc.bin(1),
                                                   "Two"  : vsc.bin(2),
                                                   "Three": vsc.bin(3)
                                               }
                                               )
            self.cp_rs1_align = vsc.coverpoint(lambda: self.instr.rs1_value[2:0],
                                               bins={
                                                   "Zero" : vsc.bin(0),
                                                   "One"  : vsc.bin(1),
                                                   "Two"  : vsc.bin(2),
                                                   "Three": vsc.bin(3)
                                               }
                                               )
            self.cp_align = vsc.cross([self.cp_imm_align, self.cp_rs1_align])
            self.cp_ras = vsc.cross([self.cp_rs1_link, self.cp_rd_link])

    '''MUL instructions'''
    @vsc.covergroup
    class mul_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
    @vsc.covergroup
    class mulh_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
    @vsc.covergroup
    class mulhsu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
    @vsc.covergroup
    class mulhu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
    @vsc.covergroup
    class div_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_e))

    @vsc.covergroup
    class divu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_ex_overflow_e))

    @vsc.covergroup
    class rem_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_e))

    @vsc.covergroup
    class remu_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_rs1_sign, self.cp_rs2_sign,
                                            self.cp_rd_sign])
            self.cp_div_result = vsc.coverpoint(lambda: self.instr.div_result,
                                                cp_t=vsc.enum_t(div_result_ex_overflow_e))

    '''CSR instructions'''

    @vsc.covergroup
    class csrrw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))

    @vsc.covergroup
    class opcode_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_opcode = vsc.coverpoint(lambda: self.instr.binary[6:2],
                                            bins={
                                                "a": vsc.bin_array([], [0, 31])
                                            }
                                            )

    @vsc.covergroup
    class rv32i_misc_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_misc = vsc.coverpoint(lambda: self.instr.instr,
                                          cp_t=vsc.enum_t(rv32i_misc_instrs))

    @vsc.covergroup
    class mepc_alignment_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_align = vsc.coverpoint(lambda: self.instr.rd_value[2:0],
                                           bins={
                                               "Zero": vsc.bin(0),
                                               "Two" : vsc.bin(2)
                                           }
                                           )

    @vsc.covergroup
    class hint_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_hint0 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                          bins=dict(addi=vsc.wildcard_bin_array([],
                                                    "0b0000_1xxx_x000_0001",
                                                    "0b0000_x1xx_x000_0001",
                                                    "0b0000_xx1x_x000_0001",
                                                    "0b0000_xxx1_x000_0001",
                                                    "0b0000_xxxx_1000_0001")))
            self.cp_hint1 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(li=vsc.wildcard_bin(
                                           "0b010x_0000_0xxx_xx01")))
            self.cp_hint2 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(lui=vsc.wildcard_bin(
                                           "0b011x_0000_0xxx_xx01")))
            self.cp_hint3 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(srli64=vsc.wildcard_bin(
                                           "0b1000_00xx_x000_0001")))
            self.cp_hint4 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(srai64=vsc.wildcard_bin(
                                           "0b1000_01xx_x000_0001")))
            self.cp_hint5 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(slli=vsc.wildcard_bin(
                                           "0b000x_0000_0xxx_xx10")))
            self.cp_hint6 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(slli64=vsc.wildcard_bin(
                                           "0b0000_xxxx_x000_0010")))
            self.cp_hint7 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(mv=vsc.wildcard_bin_array([],
                                                    "0b1000_0000_01xx_xx10",
                                                    "0b1000_0000_0x1x_xx10",
                                                    "0b1000_0000_0xx1_xx10",
                                                    "0b1000_0000_0xxx_1x10",
                                                    "0b1000_0000_0xxx_x110")))
            self.cp_hint8 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins=dict(add=vsc.wildcard_bin_array([],
                                                    "0b1001_0000_01xx_xx10",
                                                    "0b1001_0000_0x1x_xx10",
                                                    "0b1001_0000_0xx1_xx10",
                                                    "0b1001_0000_0xxx_1x10",
                                                    "0b1001_0000_0xxx_x110"
                                                 )))

    @vsc.covergroup
    class illegal_compressed_instr_cg(object):
        def __init__(self):
            super().__init__()
            self.instr = None
            self.cp_point0 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_illegal=vsc.wildcard_bin(
                                           "0b0000_0000_0000_0000")))
            self.cp_point1 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_addi4spn=vsc.wildcard_bin_array([],
                                           "0b0000_0000_000x_x100",
                                           "0b0000_0000_000x_1x00",
                                           "0b0000_0000_0001_xx00")))
            self.cp_point2 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_addiw=vsc.wildcard_bin(
                                           "0b001x_0000_0xxx_xx01")))
            self.cp_point3 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_addi16sp=vsc.wildcard_bin(
                                           "0b0110_0001_0000_0001")))
            self.cp_point4 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_lui=vsc.wildcard_bin_array([],
                                           "0b0110_xxxx_1000_0001",
                                           "0b0110_xx1x_x000_0001",
                                           "0b0110_x1xx_x000_0001",
                                           "0b0110_1xxx_x000_0001")))
            self.cp_point5 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_reserv_0=vsc.wildcard_bin(
                                           "0b1001_11xx_x10x_xx01")))
            self.cp_point6 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_reserv_1=vsc.wildcard_bin(
                                           "0b1001_11xx_x11x_xx01")))
            self.cp_point7 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_jr=vsc.wildcard_bin(
                                           "0b1000_0000_0000_0010")))
            self.cp_point8 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_lwsp=vsc.wildcard_bin(
                                           "0b010x_0000_0xxx_xx10")))
            self.cp_point9 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_lqsp=vsc.wildcard_bin(
                                           "0b001x_0000_0xxx_xx10")))
            self.cp_point10 = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                           bins = dict(c_ldsp=vsc.wildcard_bin(
                                           "0b011x_0000_0xxx_xx10")))

    '''Compressed instructions'''

    @vsc.covergroup
    class compressed_opcode_cg(object):
        # TODO issue with iff parameter
        def __init__(self):
            super().__init__()
            self.instr = None
            '''self.cp_opcode = vsc.coverpoint(lambda: self.instr.binary[15:0],
                                            bins={
                                                "a": vsc.bin_array([], [0, 31])
                                            }
                                            )'''

    @vsc.covergroup
    class c_lw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))

    @vsc.covergroup
    class c_lwsp_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(compressed_gpr))

    @vsc.covergroup
    class c_sw_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class c_swsp_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                        cp_t=vsc.enum_t(compressed_gpr))

    @vsc.covergroup
    class c_addi4spn_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class c_addi_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class c_addi16sp_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class c_li_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(store_lsu_hazard_e))

    @vsc.covergroup
    class c_lui_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_sp_t))

    @vsc.covergroup
    class c_sub_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class c_add_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                                cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class c_mv_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs2_sign = vsc.coverpoint(lambda: self.instr.rs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class c_andi_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))

    @vsc.covergroup
    class c_xor_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class c_or_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class c_and_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_rs2 = vsc.coverpoint(lambda: self.instr.rs2,
                                         cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class c_beqz_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))

    @vsc.covergroup
    class c_bnez_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))

    @vsc.covergroup
    class c_srli_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))

    @vsc.covergroup
    class c_srai_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                        cp_t=vsc.enum_t(compressed_gpr))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))

    @vsc.covergroup
    class c_slli_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(branch_hazard_e))

    @vsc.covergroup
    class c_j_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))

    @vsc.covergroup
    class c_jal_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))

    @vsc.covergroup
    class c_jr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs1_align = vsc.coverpoint(lambda: self.instr.rs1_value[1:0],
                                               bins={
                                                   "Zero" : vsc.bin(0),
                                                   "One"  : vsc.bin(1),
                                                   "Two"  : vsc.bin(2),
                                                   "Three": vsc.bin(3)
                                                    })

    @vsc.covergroup
    class c_jalr_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                        cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_rs1_align = vsc.coverpoint(lambda: self.instr.rs1_value[1:0],
                                               bins={
                                                   "Zero" : vsc.bin(0),
                                                   "One"  : vsc.bin(1),
                                                   "Two"  : vsc.bin(2),
                                                   "Three": vsc.bin(3)
                                                    })
            self.cp_rd_align = vsc.coverpoint(lambda: self.instr.rd_value[1],
                                              bins={
                                                  "Aligned"    : vsc.bin(1),
                                                  "Not-aligned": vsc.bin(0)
                                                   })
    '''Floating instructions'''

    @vsc.covergroup
    class flw_cg(object):
        def __init__(self, precision, ignore):
            super().__init__()

            self.instr = None
            self.options.ignore = ignore
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fld_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    branch_hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision), type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fsw_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    store_lsu_hazard_e))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fsd_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_ex_zero_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_imm_sign = vsc.coverpoint(lambda: self.instr.imm_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_lsu_hazard = vsc.coverpoint(lambda: self.instr.lsu_hazard,
                                                cp_t=vsc.enum_t(
                                                    store_lsu_hazard_e))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fadd_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fadd_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fsub_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fsub_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fmul_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fmul_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fdiv_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                        options = dict(weight = precision),
                                                                        type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fdiv_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fsqrt_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.bit_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.bit_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fsqrt_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fmin_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fmin_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fmax_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fmax_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fmadd_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fs3_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs3_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fmadd_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fs3_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs3_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fnmadd_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fs3_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs3_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fnmadd_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs3_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fmsub_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fs3_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                     self.instr.fs3_value[31:0],
                                                                     bins={"infinity":
                                                                            vsc.bin_array(
                                                                                [], pkg_ins.spf_val_r1,
                                                                                pkg_ins.spf_val_r2),
                                                                            "largest":
                                                                            vsc.bin_array(
                                                                                [], pkg_ins.spf_val_r1 - 1,
                                                                                pkg_ins.spf_val_r2 - 1),
                                                                            "zeros":
                                                                            vsc.bin_array(
                                                                                [], 0,
                                                                                pkg_ins.spf_zero_r),
                                                                            "NaN":
                                                                            vsc.bin_array([],
                                                                                          pkg_ins.spf_val_r1 + 1,
                                                                                          pkg_ins.spf_nan_r
                                                                                          )},
                                                                            options = dict(weight = precision),
                                                                            type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fmsub_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fs3_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs3_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fnmsub_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fs3_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                   self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs3_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                           options = dict(weight = precision),
                                                                           type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fnmsub_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs3 = vsc.coverpoint(lambda: self.instr.fs3,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs3_sign = vsc.coverpoint(lambda: self.instr.fs3_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fs3_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs3_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs3_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs3_value = vsc.coverpoint(
                lambda: self.instr.fs3_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fcvt_s_d_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_d_s_cg(object):
        def __init__(self):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_w_s_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fcvt_wu_s_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fcvt_l_s_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_lu_s_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_l_d_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_lu_d_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_w_d_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fcvt_wu_d_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fcvt_s_w_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class fcvt_s_wu_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class fcvt_s_l_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class fcvt_d_l_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_s_lu_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class fcvt_d_w_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class fcvt_d_lu_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fcvt_d_wu_cg(object):
        def __init__(self, precision, sign_typ):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class fsgnj_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fsgnj_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fsgnjn_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fsgnjn_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fsgnjx_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fsgnjx_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sign_cross = vsc.cross([self.cp_fs1_sign,
                                            self.cp_fs2_sign,
                                            self.cp_fd_sign])
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fd_value = vsc.coverpoint(lambda:
                                                                    self.instr.fd_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fd_value = vsc.coverpoint(
                lambda: self.instr.fd_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))


    @vsc.covergroup
    class fmv_x_w_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
 
    @vsc.covergroup
    class fmv_x_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_sign = vsc.coverpoint(lambda: self.instr.rd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )})
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t())
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)})
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t())

    @vsc.covergroup
    class fmv_w_x_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class fmv_d_x_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_rs1 = vsc.coverpoint(lambda: self.instr.rs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fd = vsc.coverpoint(lambda: self.instr.fd,
                                        cp_t=vsc.enum_t(riscv_fpr_t))
            self.cp_rs1_sign = vsc.coverpoint(lambda: self.instr.rs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fd_sign = vsc.coverpoint(lambda: self.instr.fd_sign,
                                             cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))

    @vsc.covergroup
    class feq_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class feq_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class flt_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class flt_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zero":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fle_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fle_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs2 = vsc.coverpoint(lambda: self.instr.fs2,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_fs2_sign = vsc.coverpoint(lambda: self.instr.fs2_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_sfp_special_values_on_fs2_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs2_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs2_value = vsc.coverpoint(
                lambda: self.instr.fs2_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))
           
    @vsc.covergroup
    class fclass_s_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_value = vsc.coverpoint(lambda: self.instr.rd_value,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    @vsc.covergroup
    class fclass_d_cg(object):
        def __init__(self, precision):
            super().__init__()

            self.instr = None
            self.cp_fs1 = vsc.coverpoint(lambda: self.instr.fs1,
                                         cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_rd = vsc.coverpoint(lambda: self.instr.rd,
                                        cp_t=vsc.enum_t(riscv_reg_t))
            self.cp_fs1_sign = vsc.coverpoint(lambda: self.instr.fs1_sign,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_rd_value = vsc.coverpoint(lambda: self.instr.rd_value,
                                              cp_t=vsc.enum_t(operand_sign_e))
            self.cp_gpr_hazard = vsc.coverpoint(lambda: self.instr.gpr_hazard,
                                                cp_t=vsc.enum_t(hazard_e))
            self.cp_sfp_special_values_on_fs1_value = vsc.coverpoint(lambda:
                                                                    self.instr.fs1_value[31:0],
                                                                    bins={"infinity":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1,
                                                                              pkg_ins.spf_val_r2),
                                                                          "largest":
                                                                          vsc.bin_array(
                                                                              [], pkg_ins.spf_val_r1 - 1,
                                                                              pkg_ins.spf_val_r2 - 1),
                                                                          "zeros":
                                                                          vsc.bin_array(
                                                                              [], 0,
                                                                              pkg_ins.spf_zero_r),
                                                                          "NaN":
                                                                          vsc.bin_array([],
                                                                                        pkg_ins.spf_val_r1 + 1,
                                                                                        pkg_ins.spf_nan_r
                                                                                        )},
                                                                          options = dict(weight = precision),
                                                                          type_options = dict(weight = precision))
            self.cp_sfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[30:pkg_ins.SINGLE_PRECISION_FRACTION_BITS] == 0,
                cp_t =vsc.int32_t(), options = dict(weight = precision),type_options = dict(weight = precision))
            self.cp_dfp_special_values_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value, bins={
                    "infinity": vsc.bin_array([], pkg_ins.dpf_val_r1, pkg_ins.dpf_val_r2),
                    "largest": vsc.bin_array([], pkg_ins.dpf_val_r1 - 1, pkg_ins.dpf_val_r2 - 1),
                    "zeros": vsc.bin_array([], 0, pkg_ins.dpf_zero_r),
                    "NaN": vsc.bin_array([], pkg_ins.dpf_val_r1 + 1, pkg_ins.dpf_nan_r)},
                    options = dict(weight = not precision),type_options = dict(weight = not precision))
            self.cp_dfp_subnormal_on_fs1_value = vsc.coverpoint(
                lambda: self.instr.fs1_value[62:pkg_ins.DOUBLE_PRECISION_FRACTION_BITS - 1] == 0,
                cp_t=vsc.bit_t(), options = dict(weight = not precision),type_options = dict(weight = not precision))

    def cg_instantiation(self):
        self.opcode_cg_i = self.opcode_cg()
        self.csrrw_cg_i = self.csrrw_cg()
        self.rv32i_misc_cg_i = self.rv32i_misc_cg()
        self.mepc_alignment_cg_i = self.mepc_alignment_cg()
        # self.compressed_opcode_cg_i = self.compressed_opcode_cg()
        self.beq_cg_i = self.beq_cg()
        self.jal_cg_i = self.jal_cg()
        self.lui_cg_i = self.lui_cg()
        self.addi_cg_i = self.addi_cg()
        self.auipc_cg_i = self.auipc_cg()
        self.ori_cg_i = self.ori_cg()
        self.add_cg_i = self.add_cg()
        self.sub_cg_i = self.sub_cg()
        self.sra_cg_i = self.sra_cg()
        self.andi_cg_i = self.andi_cg()
        self.srli_cg_i = self.srli_cg()
        self.and_cg_i = self.and_cg()
        self.srl_cg_i = self.srl_cg()
        self.sll_cg_i = self.sll_cg()
        self.xor_cg_i = self.xor_cg()
        self.or_cg_i = self.or_cg()
        self.sltu_cg_i = self.sltu_cg()
        self.sltiu_cg_i = self.sltiu_cg()
        self.xori_cg_i = self.xori_cg()
        self.slti_cg_i = self.slti_cg()
        self.srai_cg_i = self.srai_cg()
        self.slt_cg_i = self.slt_cg()
        self.slli_cg_i = self.slli_cg()
        self.mul_cg_i = self.mul_cg()
        self.mulh_cg_i = self.mulh_cg()
        self.mulhsu_cg_i = self.mulhsu_cg()
        self.mulhu_cg_i = self.mulhu_cg()
        self.div_cg_i = self.div_cg()
        self.divu_cg_i = self.divu_cg()
        self.rem_cg_i = self.rem_cg()
        self.remu_cg_i = self.remu_cg()
        self.c_lw_cg_i = self.c_lw_cg()
        self.c_lwsp_cg_i = self.c_lwsp_cg()
        self.c_sw_cg_i = self.c_sw_cg()
        self.c_swsp_cg_i = self.c_swsp_cg()
        self.c_addi4spn_cg_i = self.c_addi4spn_cg()
        self.c_addi_cg_i = self.c_addi_cg()
        self.c_addi16sp_cg_i = self.c_addi16sp_cg()
        self.c_li_cg_i = self.c_li_cg()
        self.c_lui_cg_i = self.c_lui_cg()
        self.c_sub_cg_i = self.c_sub_cg()
        self.c_add_cg_i = self.c_add_cg()
        self.c_mv_cg_i = self.c_mv_cg()
        self.c_andi_cg_i = self.c_andi_cg()
        self.c_xor_cg_i = self.c_xor_cg()
        self.c_or_cg_i = self.c_or_cg()
        self.c_and_cg_i = self.c_and_cg()
        self.c_beqz_cg_i = self.c_beqz_cg()
        self.c_bnez_cg_i = self.c_bnez_cg()
        self.c_srli_cg_i = self.c_srli_cg()
        self.c_srai_cg_i = self.c_srai_cg()
        self.c_slli_cg_i = self.c_slli_cg()
        self.c_j_cg_i = self.c_j_cg()
        self.c_jal_cg_i = self.c_jal_cg()
        self.c_jr_cg_i = self.c_jr_cg()
        self.c_jalr_cg_i = self.c_jalr_cg()
        self.hint_cg_i = self.hint_cg()
        self.illegal_compressed_instr_cg_i = self.illegal_compressed_instr_cg()
        self.flw_cg_i = self.flw_cg(1, 0)
        self.fld_cg_i = self.fld_cg(0)
        self.fsw_cg_i = self.fsw_cg(1)
        self.fsw_cg_i = self.fsw_cg(0)
        self.fadd_s_cg_i = self.fadd_s_cg(1)
        self.fadd_d_cg_i = self.fadd_d_cg(0)
        self.fsub_s_cg_i = self.fsub_s_cg(1)
        self.fsub_d_cg_i = self.fsub_d_cg(0)
        self.fmul_s_cg_i = self.fmul_s_cg(1)
        self.fmul_d_cg_i = self.fmul_d_cg(0)
        self.fdiv_s_cg_i = self.fdiv_s_cg(1)
        self.fdiv_d_cg_i = self.fdiv_d_cg(0)
        self.fsqrt_s_cg_i = self.fsqrt_s_cg(1)
        self.fsqrt_d_cg_i = self.fsqrt_d_cg(0)
        self.fmin_s_cg_i = self.fmin_s_cg(1)
        self.fmin_d_cg_i = self.fmin_d_cg(0)
        self.fmax_s_cg_i = self.fmax_s_cg(1)
        self.fmax_d_cg_i = self.fmax_d_cg(0)
        self.fmadd_s_cg_i = self.fmadd_s_cg(1)
        self.fmadd_d_cg_i = self.fmadd_d_cg(0)
        self.fnmadd_s_cg_i = self.fnmadd_s_cg(1)
        self.fnmadd_d_cg_i = self.fnmadd_d_cg(0)
        self.fmsub_s_cg_i = self.fmsub_s_cg(1)
        self.fmsub_d_cg_i = self.fmsub_d_cg(0)
        self.fnmsub_s_cg_i = self.fnmsub_s_cg(1)
        self.fnmsub_d_cg_i = self.fnmsub_d_cg(0)
        self.fcvt_s_d_cg_i = self.fcvt_s_d_cg()
        self.fcvt_d_s_cg_i = self.fcvt_d_s_cg()
        self.fcvt_w_s_cg_i = self.fcvt_w_s_cg(1,'sign')
        self.fcvt_wu_s_cg_i = self.fcvt_wu_s_cg(1,'unsign')
        self.fcvt_l_s_cg_i = self.fcvt_l_s_cg(1,'sign')
        self.fcvt_lu_s_cg_i = self.fcvt_lu_s_cg(1,'unsign')
        self.fcvt_l_d_cg_i = self.fcvt_l_d_cg(0,'sign')
        self.fcvt_lu_d_cg_i = self.fcvt_lu_d_cg(0,'unsign')
        self.fcvt_w_d_cg_i = self.fcvt_w_d_cg(0,'sign')
        self.fcvt_wu_d_cg_i = self.fcvt_wu_d_cg(0,'unsign')
        self.fcvt_s_w_cg_i = self.fcvt_s_w_cg(1,'sign')
        self.fcvt_s_wu_cg_i = self.fcvt_s_wu_cg(1,'unsign')
        self.fcvt_s_l_cg_i = self.fcvt_s_l_cg(1,'sign')
        self.fcvt_d_l_cg_i = self.fcvt_d_l_cg(1,'sign')
        self.fcvt_s_lu_cg_i = self.fcvt_s_lu_cg(1,'unsign')
        self.fcvt_d_w_cg_i = self.fcvt_d_w_cg(0,'sign')
        self.fcvt_d_lu_cg_i = self.fcvt_d_lu_cg(0,'unsign')
        self.fcvt_d_wu_cg_i = self.fcvt_d_wu_cg(0,'unsign')
        self.fsgnj_s_cg_i = self.fsgnj_s_cg(1)
        self.fsgnj_d_cg_i = self.fsgnj_d_cg(0)
        self.fsgnjn_s_cg_i = self.fsgnjn_s_cg(1)
        self.fsgnjn_d_cg_i = self.fsgnjn_d_cg(0)
        self.fsgnjx_s_cg_i = self.fsgnjx_s_cg(1)
        self.fsgnjx_d_cg_i = self.fsgnjx_d_cg(0)
        self.fmv_x_w_cg_i = self.fmv_x_w_cg(1)
        self.fmv_x_d_cg_i = self.fmv_x_d_cg(0)
        self.fmv_w_x_cg_i = self.fmv_w_x_cg(1)
        self.fmv_d_x_cg_i = self.fmv_d_x_cg(0)
        self.feq_s_cg_i = self.feq_s_cg(1)
        self.feq_d_cg_i = self.feq_d_cg(0)
        self.flt_s_cg_i = self.flt_s_cg(1)
        self.flt_d_cg_i = self.flt_d_cg(0)
        self.fle_s_cg_i = self.fle_s_cg(1)
        self.fle_d_cg_i = self.fle_d_cg(0)
        self.fclass_s_cg_i = self.fclass_s_cg(1)
        self.fclass_d_cg_i = self.fclass_d_cg(0)
        self.mulw_cg_i = self.mulw_cg()
        self.divw_cg_i = self.divw_cg()
        self.divuw_cg_i = self.divuw_cg()
        self.remw_cg_i = self.remw_cg()
        self.remuw_cg_i = self.remuw_cg()
        self.c_addiw_cg_i = self.c_addiw_cg()
        self.c_subw_cg_i = self.c_subw_cg()
        self.c_addw_cg_i = self.c_addw_cg()
        self.c_ld_cg_i = self.c_ld_cg()
        self.c_sd_cg_i = self.c_sd_cg()
        self.c_ldsp_cg_i = self.c_ldsp_cg()
        self.c_sdsp_cg_i = self.c_sdsp_cg()
        self.lwu_cg_i = self.lwu_cg()
        self.ld_cg_i = self.ld_cg()
        self.sd_cg_i = self.sd_cg()
        self.addiw_cg_i = self.addiw_cg()
        self.slliw_cg_i = self.slliw_cg()
        self.srliw_cg_i = self.srliw_cg()
        self.sraiw_cg_i = self.sraiw_cg()
        self.addw_cg_i = self.addw_cg()
        self.subw_cg_i = self.subw_cg()
        self.sllw_cg_i = self.sllw_cg()
        self.srlw_cg_i = self.srlw_cg()
        self.sraw_cg_i = self.sraw_cg()


    def sample(self, instr):
        self.instr_cnt += 1
        if self.instr_cnt > 1:
            instr.check_hazard_condition(self.pre_instr)
        # TODO: sampling for compressed_instr_cg
        if ((instr.binary[1:0] != 3) and (riscv_instr_group_t.RV32C in rcs.supported_isa)):
            # self.compressed_opcode_cg_i.instr = instr
            # self.compressed_opcode_cg_i.sample()
            self.hint_cg_i.instr = instr
            self.hint_cg_i.sample()
            self.illegal_compressed_instr_cg_i.instr = instr
            self.illegal_compressed_instr_cg_i.sample()

        if instr.binary[1:0] == 3:
            self.opcode_cg_i.instr = instr
            self.opcode_cg_i.sample()
        try:
            setattr(eval("self." + instr.instr.name.lower() + "_cg_i"),
                    'instr', instr)
            eval("self." + instr.instr.name.lower() + "_cg_i" + ".sample()")
        except Exception:
            logging.info("Covergroup for instr {} is not supported yet".format(
                instr.instr.name))
            # Trace the error if there is an Exception
            logging.info("Traceback error log: {}".format(traceback.format_exc()))

        if instr.group.name == "RV32I":
            self.rv32i_misc_cg_i.instr = instr
            self.rv32i_misc_cg_i.sample()
        if instr.category.name == "CSR":
            # MEPC
            if instr.csr == 833:
                self.mepc_alignment_cg_i.instr = instr
                self.mepc_alignment_cg_i.sample()
        self.pre_instr = instr

    def reset(self):
        self.instr_cnt = 0
        self.branch_instr_cnt = 0
        self.branch_hit_history.set_val(0)
