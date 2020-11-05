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
            self.cp_opcode = vsc.coverpoint(lambda: self.instr.binary[7:2],
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

    def cg_instantiation(self):
        self.opcode_cg_i = self.opcode_cg()
        self.csrrw_cg_i = self.csrrw_cg()
        self.rv32i_misc_cg_i = self.rv32i_misc_cg()
        self.mepc_alignment_cg_i = self.mepc_alignment_cg()
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

    def sample(self, instr):
        self.instr_cnt += 1
        if self.instr_cnt > 1:
            instr.check_hazard_condition(self.pre_instr)
        # TODO: sampling for hint, compressed, and illegal_compressed insts
        if instr.binary[2:0] == 3:
            self.opcode_cg_i.instr = instr
            self.opcode_cg_i.sample()
        try:
            setattr(eval("self." + instr.instr.name.lower() + "_cg_i"),
                    'instr', instr)
            eval("self." + instr.instr.name.lower() + "_cg_i" + ".sample()")
        except Exception:
            logging.info("Covergroup for instr {} is not supported yet".format(
                instr.instr.name))
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
