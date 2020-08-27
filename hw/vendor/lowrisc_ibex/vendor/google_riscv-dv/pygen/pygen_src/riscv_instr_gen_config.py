"""
Copyright 2020 Google LLC
Copyright 2020 PerfectVIPs Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.

"""

import argparse
import logging
import sys
import vsc
from bitstring import BitArray
from pygen_src.riscv_instr_pkg import mtvec_mode_t, f_rounding_mode_t, \
    riscv_reg_t, privileged_mode_t, \
    riscv_instr_group_t
from pygen_src.target.rv32i import riscv_core_setting as rcs


@vsc.randobj
class riscv_instr_gen_config:
    def __init__(self, argv):
        # TODO Support for command line argument
        self.main_program_instr_cnt = 100  # count of main_prog
        self.sub_program_instr_cnt = []  # count of sub_prog
        self.debug_program_instr_cnt = 0  # count of debug_rom
        self.debug_sub_program_instr_cnt = []  # count of debug sub_progrms
        # Commenting out for now
        # self.data_page_pattern = list(
        # map(lambda dta_pg: dta_pg.name, data_pattern_t))
        # dicts for exception_cause_t & interrupt_cause_t Enum classes

        self.m_mode_exception_delegation = {}
        self.s_mode_exception_delegation = {}
        self.m_mode_interrupt_delegation = {}
        self.s_mode_interrupt_delegation = {}

        # init_privileged_mode default to MACHINE_MODE
        self.init_privileged_mode = privileged_mode_t.MACHINE_MODE

        self.mstatus = BitArray(bin(0b0), length=rcs.XLEN - 1)
        self.mie = BitArray(bin(0b0), length=rcs.XLEN - 1)
        self.sstatus = BitArray(bin(0b0), length=rcs.XLEN - 1)
        self.sie = BitArray(bin(0b0), length=rcs.XLEN - 1)
        self.ustatus = BitArray(bin(0b0), length=rcs.XLEN - 1)
        self.uie = BitArray(bin(0b0), length=rcs.XLEN - 1)

        self.mstatus_mprv = 0
        self.mstatus_mxr = 0
        self.mstatus_sum = 0
        self.mstatus_tvm = 0
        self.mstatus_fs = BitArray(bin(0b0), length=2)
        self.mstatus_vs = BitArray(bin(0b0), length=2)
        self.mtvec_mode = vsc.rand_enum_t(mtvec_mode_t)

        self.tvec_alignment = argv.tvec_alignment

        self.fcsr_rm = list(map(lambda csr_rm: csr_rm.name, f_rounding_mode_t))
        self.enable_sfence = 0
        self.gpr = []

        # Helper fields for gpr
        self.gpr0 = vsc.rand_enum_t(riscv_reg_t)
        self.gpr1 = vsc.rand_enum_t(riscv_reg_t)
        self.gpr2 = vsc.rand_enum_t(riscv_reg_t)
        self.gpr3 = vsc.rand_enum_t(riscv_reg_t)

        self.scratch_reg = vsc.rand_enum_t(riscv_reg_t)
        self.pmp_reg = vsc.rand_enum_t(riscv_reg_t)
        self.sp = vsc.rand_enum_t(riscv_reg_t)
        self.tp = vsc.rand_enum_t(riscv_reg_t)
        self.ra = vsc.rand_enum_t(riscv_reg_t)
        self.check_misa_init_val = 0
        self.check_xstatus = 1
        self.virtual_addr_translation_on = 0

        # Commenting out for now
        # vector_cfg = riscv_vector_cfg # TODO
        # pmp_cfg = riscv_pmp_cfg  # TODO
        # self.mem_region = [] # TODO
        # Self.amo_region = [] # TODO

        self.stack_len = 5000

        # Self.s_mem_region = [] # TODO

        self.kernel_stack_len = 4000
        self.kernel_program_instr_cnt = 400
        # list of main implemented CSRs
        self.invalid_priv_mode_csrs = []
        self.num_of_sub_program = argv.num_of_sub_program
        self.instr_cnt = argv.instr_cnt
        self.num_of_tests = argv.num_of_tests
        self.no_data_page = argv.no_data_page
        self.no_branch_jump = argv.no_branch_jump
        self.no_load_store = argv.no_load_store
        self.no_csr_instr = argv.no_csr_instr
        self.no_ebreak = argv.no_ebreak
        self.no_dret = argv.no_dret
        self.no_fence = argv.no_fence
        self.no_wfi = argv.no_wfi
        self.enable_unaligned_load_store = argv.enable_unaligned_load_store
        self.illegal_instr_ratio = argv.illegal_instr_ratio
        self.hint_instr_ratio = argv.hint_instr_ratio
        self.num_of_harts = argv.num_of_harts
        self.fix_sp = argv.fix_sp
        self.use_push_data_section = argv.use_push_data_section
        self.boot_mode_opts = argv.boot_mode_opts

        if(self.boot_mode_opts):
            logging.info("Got boot mode option - %0s", self.boot_mode_opts)
            if(self.boot_mode_opts == "m"):
                self.init_privileged_mode = privileged_mode_t.MACHINE_MODE.name
            elif(self.boot_mode_opts == "s"):
                self.init_privileged_mode = privileged_mode_t.SUPERVISOR_MODE.name
            elif(self.boot_mode_opts == "u"):
                self.init_privileged_mode = privileged_mode_t.USER_MODE.name
            else:
                logging.error("Illegal boot mode option - %0s", self.boot_mode_opts)

        self.enable_page_table_exception = argv.enable_page_table_exception
        self.no_directed_instr = argv.no_directed_instr
        self.asm_test_suffix = argv.asm_test_suffix
        self.enable_interrupt = argv.enable_interrupt
        self.enable_nested_interrupt = argv.enable_nested_interrupt
        self.enable_timer_irq = argv.enable_timer_irq
        self.bare_program_mode = argv.bare_program_mode
        self.enable_illegal_csr_instruction = argv.enable_illegal_csr_instruction
        self.enable_access_invalid_csr_level = argv.enable_access_invalid_csr_level
        self.enable_misaligned_instr = argv.enable_misaligned_instr
        self.enable_dummy_csr_write = argv.enable_dummy_csr_write
        self.randomize_csr = argv.randomize_csr
        self.allow_sfence_exception = argv.allow_sfence_exception
        self.no_delegation = argv.no_delegation
        self.force_m_delegation = argv.force_m_delegation
        self.force_s_delegation = argv.force_s_delegation
        self.support_supervisor_mode = 0
        self.disable_compressed_instr = argv.disable_compressed_instr
        self.require_signature_addr = argv.require_signature_addr

        if(self.require_signature_addr):
            self.signature_addr = int(argv.signature_addr, 16)
        else:
            self.signature_addr = 0xdeadbeef

        self.gen_debug_section = argv.gen_debug_section
        self.enable_ebreak_in_debug_rom = argv.enable_ebreak_in_debug_rom
        self.set_dcsr_ebreak = argv.set_dcsr_ebreak
        self.num_debug_sub_program = argv.num_debug_sub_program
        self.enable_debug_single_step = argv.enable_debug_single_step
        self.single_step_iterations = 0
        self.set_mstatus_tw = argv.set_mstatus_tw
        self.set_mstatus_mprv = argv.set_mstatus_mprv
        self.min_stack_len_per_program = 10 * (rcs.XLEN / 8)
        self.max_stack_len_per_program = 16 * (rcs.XLEN / 8)
        self.max_branch_step = 20
        self.max_directed_instr_stream_seq = 20
        self.reserved_regs = vsc.list_t(vsc.enum_t(riscv_reg_t))
        self.enable_floating_point = argv.enable_floating_point
        self.enable_vector_extension = argv.enable_vector_extension
        self.enable_b_extension = argv.enable_b_extension
        self.enable_bitmanip_groups = argv.enable_bitmanip_groups
        self.dist_control_mode = 0
        self.category_dist = {}
        self.march_isa = argv.march_isa

        if(len(self.march_isa) != 0):
            rcs.supported_isa = self.march_isa

        if(rcs.supported_isa != 'RV32C'):
            self.disable_compressed_instr = 1

    @vsc.constraint
    def gpr_c(self):
        self.gpr0.not_inside(vsc.rangelist(self.sp, self.tp, self.scratch_reg, self.pmp_reg,
                                           riscv_reg_t.ZERO, riscv_reg_t.RA, riscv_reg_t.GP))
        self.gpr1.not_inside(vsc.rangelist(self.sp, self.tp, self.scratch_reg, self.pmp_reg,
                                           riscv_reg_t.ZERO, riscv_reg_t.RA, riscv_reg_t.GP))
        self.gpr2.not_inside(vsc.rangelist(self.sp, self.tp, self.scratch_reg, self.pmp_reg,
                                           riscv_reg_t.ZERO, riscv_reg_t.RA, riscv_reg_t.GP))
        self.gpr3.not_inside(vsc.rangelist(self.sp, self.tp, self.scratch_reg, self.pmp_reg,
                                           riscv_reg_t.ZERO, riscv_reg_t.RA, riscv_reg_t.GP))
        vsc.unique(self.gpr0, self.gpr1, self.gpr2, self.gpr3)

    def check_setting(self):
        support_64b = 0
        support_128b = 0

        # list of satp_mode_t from riscv_core_setting.py
        stp_md_lst = rcs.SATP_MODE

        # list of riscv_instr_group_t with names of riscv_instr_name_t in it.
        supported_isa_lst = list(map(lambda z: z.name, riscv_instr_group_t))

        # check the valid isa support
        for x in rcs.supported_isa:
            if x == (supported_isa_lst[1] or supported_isa_lst[3] or supported_isa_lst[5] or
                     supported_isa_lst[8] or supported_isa_lst[11] or supported_isa_lst[13] or
                     supported_isa_lst[19]):
                support_64b = 1
                logging.info("support_64b=%d" % support_64b)
                logging.debug("Supported ISA=%s" % x)
            elif x == (supported_isa_lst[14] or supported_isa_lst[15]):
                support_128b = 1
                logging.info("support_128b=%d" % support_128b)
                logging.debug("Supported ISA=%s" % x)

        if (support_128b == 1) and (rcs.XLEN != 128):
            logging.critical("XLEN should be set to 128 based on \
                              riscv_core_setting.supported_isa setting")
            logging.info("XLEN Value=%d" % rcs.XLEN)
            sys.exit("XLEN is not equal to 128, set it Accordingly!")

        if (support_128b == 0) and (support_64b == 1) and (rcs.XLEN != 64):
            logging.critical("XLEN should be set to 64 based on \
                              riscv_core_setting.supported_isa setting")
            logging.info("XLEN Value=%d" % rcs.XLEN)
            sys.exit("XLEN is not equal to 64, set it Accordingly!")

        if not(support_128b or support_64b) and (rcs.XLEN != 32):
            logging.critical("XLEN should be set to 32 based on \
                              riscv_core_setting.supported_isa setting")
            logging.info("XLEN Value=%d" % rcs.XLEN)
            sys.exit("XLEN is not equal to 32, set it Accordingly!")

        if not(support_128b or support_64b) and not(('SV32' in stp_md_lst) or
                                                    ('BARE' in stp_md_lst)):
            logging.critical("SATP mode is not supported for RV32G ISA")
            logging.info(stp_md_lst)
            sys.exit("Supported SATP mode is not provided")

    # TODO
    def setup_instr_distribution(self):
        pass

    def init_delegation(self):
        for i in self.mode_exp_lst:
            if i == self.mode_exp_lst[0]:
                continue
            self.m_mode_exception_delegation[i] = 0
            self.s_mode_exception_delegation[i] = 0

        for j in self.mode_intrpt_lst:
            if j == self.mode_intrpt_lst[0]:
                continue
            self.m_mode_interrupt_delegation[j] = 0
            self.s_mode_interrupt_delegation[j] = 0

    def pre_randomize(self):
        # Clearing the contents of self.gpr after each randomization.
        # As it is being extended in post_randomize function.
        self.gpr.clear()
        for x in rcs.supported_privileged_mode:
            if(x == "SUPERVISOR_MODE"):
                self.support_supervisor_mode = 1

    def get_non_reserved_gpr(self):
        pass

    def post_randomize(self):
        # Temporary fix for gpr_c constraint.
        self.gpr.extend((self.gpr0, self.gpr1, self.gpr2, self.gpr3))

        self.reserved_regs.append(self.tp)
        self.reserved_regs.append(self.sp)
        self.reserved_regs.append(self.scratch_reg)
        self.min_stack_len_per_program = 2 * (rcs.XLEN / 8)
        logging.info("min_stack_len_per_program value = %d"
                     % self.min_stack_len_per_program)
        self.check_setting()  # to check the setting is legal

        # TODO, Need to change the logic once the constraints are up.
        if "USER_MODE" == self.init_privileged_mode:
            logging.info("mode=%s" % "USER_MODE")
            self.no_wfi = 1

    def get_invalid_priv_lvl_csr(self):
        invalid_lvl = []
        # Debug CSRs are inaccessible from all but Debug Mode
        # and we cannot boot into Debug Mode.
        invalid_lvl.append('D')

        # TODO Need to change the logic once the constraints are up.
        for mode in self.init_privileged_mode:
            if mode == "MACHINE_MODE":
                continue
            if mode == 'SUPERVISOR_MODE':
                invalid_lvl.append('M')
                logging.info("supr_mode---")
                logging.debug(invalid_lvl)
            elif mode == 'USER_MODE':
                invalid_lvl.append('S')
                invalid_lvl.append('M')
                logging.info("usr_mode---")
                logging.debug(invalid_lvl)
            else:
                logging.critical("Unsupported initialization privilege mode")

        # implemented_csr from riscv_core_setting.py
        for x in rcs.implemented_csr:
            if x[0] in invalid_lvl:
                self.invalid_priv_mode_csrs.append(x)

    # This function calls all the above defined function which should
    # be called in init function as per SV logic.This function as to be
    # called after every instance of the gen_config handle
    def func_call_init(self):
        self.init_delegation()
        # self.setup_instr_distribution()  # TODO
        self.get_invalid_priv_lvl_csr()


def parse_args():
    parse = argparse.ArgumentParser()
    parse.add_argument('--num_of_tests', help = 'num_of_tests', type = int, default = 1)
    parse.add_argument('--enable_page_table_exception',
                       help = 'enable_page_table_exception', type = int, default = 0)
    parse.add_argument('--enable_interrupt', help = 'enable_interrupt',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_nested_interrupt', help = 'enable_nested_interrupt',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_timer_irq', help = 'enable_timer_irq',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--num_of_sub_program', help = 'num_of_sub_program', type = int, default = 5)
    parse.add_argument('--instr_cnt', help = 'instr_cnt', type = int, default = 200)
    parse.add_argument('--tvec_alignment', help = 'tvec_alignment', type = int, default = 2)
    parse.add_argument('--no_ebreak', help = 'no_ebreak', choices = [0, 1], type = int, default = 1)
    parse.add_argument('--no_dret', help = 'no_dret', choices = [0, 1], type = int, default = 1)
    parse.add_argument('--no_wfi', help = 'no_wfi', choices = [0, 1], type = int, default = 1)

    parse.add_argument('--no_branch_jump', help = 'no_branch_jump',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--no_load_store', help = 'no_load_store',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--no_csr_instr', help = 'no_csr_instr',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--fix_sp', help = 'fix_sp', choices = [0, 1], type = int, default = 0)
    parse.add_argument('--use_push_data_section', help = 'use_push_data_section',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_illegal_csr_instruction',
                       help = 'enable_illegal_csr_instruction', choices = [0, 1],
                       type = int, default = 0)
    parse.add_argument('--enable_access_invalid_csr_level',
                       help = 'enable_access_invalid_csr_level', choices = [0, 1],
                       type = int, default = 0)
    parse.add_argument('--enable_misaligned_instr', help = 'enable_misaligned_instr',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_dummy_csr_write', help = 'enable_dummy_csr_write',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--allow_sfence_exception', help = 'allow_sfence_exception',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--no_data_page', help = 'no_data_page',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--no_directed_instr', help = 'no_directed_instr',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--no_fence', help = 'no_fence', choices = [0, 1], type = int, default = 1)
    parse.add_argument('--no_delegation', help = 'no_delegation',
                       choices = [0, 1], type = int, default = 1)
    parse.add_argument('--illegal_instr_ratio',
                       help = 'illegal_instr_ratio', type = int, default = 0)
    parse.add_argument('--hint_instr_ratio', help = 'hint_instr_ratio', type = int, default = 0)
    parse.add_argument('--num_of_harts', help = 'num_of_harts', type = int, default = rcs.NUM_HARTS)
    parse.add_argument('--enable_unaligned_load_store',
                       help = 'enable_unaligned_load_store', choices = [0, 1],
                       type = int, default = 0)
    parse.add_argument('--force_m_delegation', help = 'force_m_delegation',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--force_s_delegation', help = 'force_s_delegation',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--require_signature_addr', help = 'require_signature_addr',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--signature_addr', help = 'signature_addr', default = 0xdeadbeef)
    parse.add_argument('--disable_compressed_instr',
                       help = 'disable_compressed_instr', choices = [0, 1], type = int, default = 0)
    parse.add_argument('--randomize_csr', help = 'randomize_csr',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--gen_debug_section', help = 'gen_debug_section',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--bare_program_mode', help = 'bare_program_mode',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--num_debug_sub_program',
                       help = 'num_debug_sub_program', type = int, default = 0)
    parse.add_argument('--enable_ebreak_in_debug_rom',
                       help = 'enable_ebreak_in_debug_rom', choices = [0, 1],
                       type = int, default = 0)
    parse.add_argument('--set_dcsr_ebreak', help = 'set_dcsr_ebreak',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_debug_single_step',
                       help = 'enable_debug_single_step', choices = [0, 1], type = int, default = 0)
    parse.add_argument('--set_mstatus_tw', help = 'set_mstatus_tw',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--set_mstatus_mprv', help = 'set_mstatus_mprv',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_floating_point', help = 'enable_floating_point',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_vector_extension', help = 'enable_vector_extension',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_b_extension', help = 'enable_b_extension',
                       choices = [0, 1], type = int, default = 0)
    parse.add_argument('--enable_bitmanip_groups', help = 'enable_bitmanip_groups',
                       default = ['ZBB', 'ZBS', 'ZBP', 'ZBE', 'ZBF',
                                  'ZBC', 'ZBR', 'ZBM', 'ZBT', 'ZB_TMP'], nargs = '*')
    parse.add_argument('--boot_mode_opts', help = 'boot_mode_opts', default = "")
    parse.add_argument('--asm_test_suffix', help = 'asm_test_suffix', default = "")
    parse.add_argument('--march_isa', help = 'march_isa', default = [],
                       choices = [i.name for i in riscv_instr_group_t], nargs = '*')
    parse.add_argument('--directed_instr_0', help = 'directed_instr_0',
                       default = "riscv_int_numeric_corner_stream,4")
    parse.add_argument('--stream_name_opts', help = 'stream_name_0',
                       default = "riscv_load_store_rand_instr_stream")
    parse.add_argument('--stream_freq_opts', help = 'stream_freq_0', default = 4)
    # TODO
    '''
    if ($value$plusargs("tvec_alignment=%0d", tvec_alignment)) begin
        tvec_alignment.rand_mode(0);
    end

    vector_cfg = riscv_vector_cfg::type_id::create("vector_cfg");
    pmp_cfg = riscv_pmp_cfg::type_id::create("pmp_cfg");
    pmp_cfg.rand_mode(pmp_cfg.pmp_randomize);
    pmp_cfg.initialize(require_signature_addr);
    setup_instr_distribution();
    get_invalid_priv_lvl_csr();
    '''
    args = parse.parse_args()
    return args


args = parse_args()
args_dict = vars(args)
cfg = riscv_instr_gen_config(args)
