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

import sys
import math
import logging
import argparse
import vsc
from importlib import import_module
from pygen_src.riscv_instr_pkg import (mtvec_mode_t, f_rounding_mode_t,
                                       riscv_reg_t, privileged_mode_t,
                                       riscv_instr_group_t, data_pattern_t,
                                       riscv_instr_category_t, satp_mode_t,
                                       mem_region_t)


@vsc.randobj
class riscv_instr_gen_config:
    def __init__(self):
        self.main_program_instr_cnt = vsc.rand_int32_t()  # count of main_prog
        self.sub_program_instr_cnt = []  # count of sub_prog
        self.debug_program_instr_cnt = 0  # count of debug_rom
        self.debug_sub_program_instr_cnt = []  # count of debug sub_progrms
        self.max_directed_instr_stream_seq = 20
        self.data_page_pattern = vsc.rand_enum_t(data_pattern_t)

        self.init_delegation()
        self.argv = self.parse_args()
        self.args_dict = vars(self.argv)

        global rcs
        rcs = import_module("pygen_src.target." + self.argv.target + ".riscv_core_setting")

        self.m_mode_exception_delegation = {}
        self.s_mode_exception_delegation = {}
        self.m_mode_interrupt_delegation = {}
        self.s_mode_interrupt_delegation = {}

        # init_privileged_mode default to MACHINE_MODE
        self.init_privileged_mode = privileged_mode_t.MACHINE_MODE

        self.mstatus = vsc.rand_bit_t(rcs.XLEN - 1)
        self.mie = vsc.rand_bit_t(rcs.XLEN - 1)
        self.sstatus = vsc.rand_bit_t(rcs.XLEN - 1)
        self.sie = vsc.rand_bit_t(rcs.XLEN - 1)
        self.ustatus = vsc.rand_bit_t(rcs.XLEN - 1)
        self.uie = vsc.rand_bit_t(rcs.XLEN - 1)

        self.mstatus_mprv = vsc.rand_bit_t(1)
        self.mstatus_mxr = vsc.rand_bit_t(1)
        self.mstatus_sum = vsc.rand_bit_t(1)
        self.mstatus_tvm = vsc.rand_bit_t(1)
        self.mstatus_fs = vsc.rand_bit_t(2)
        self.mstatus_vs = vsc.rand_bit_t(2)
        self.mtvec_mode = vsc.rand_enum_t(mtvec_mode_t)

        self.tvec_alignment = vsc.rand_uint8_t(self.argv.tvec_alignment)

        self.fcsr_rm = vsc.rand_enum_t(f_rounding_mode_t)
        self.enable_sfence = vsc.rand_bit_t(1)
        self.gpr = vsc.rand_list_t(vsc.enum_t(riscv_reg_t), sz=4)

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

        self.mem_region = vsc.list_t(mem_region_t())
        self.amo_region = vsc.list_t(mem_region_t())
        self.s_mem_region = vsc.list_t(mem_region_t())
        self.mem_region.extend([mem_region_t(name = "region_0", size_in_bytes = 4096, xwr = 8),
                                mem_region_t(name = "region_1", size_in_bytes = 4096, xwr = 8)])
        self.amo_region.extend([mem_region_t(name = "amo_0", size_in_bytes = 64, xwr = 8)])
        self.s_mem_region.extend([mem_region_t(name = "s_region_0", size_in_bytes = 4096, xwr = 8),
                                  mem_region_t(name = "s_region_1", size_in_bytes = 4096, xwr = 8)])

        self.stack_len = 5000
        self.kernel_stack_len = 4000
        self.kernel_program_instr_cnt = 400
        # list of main implemented CSRs
        self.invalid_priv_mode_csrs = []
        self.num_of_sub_program = self.argv.num_of_sub_program
        self.instr_cnt = self.argv.instr_cnt
        self.num_of_tests = self.argv.num_of_tests
        self.no_data_page = self.argv.no_data_page
        self.no_branch_jump = self.argv.no_branch_jump
        self.no_load_store = self.argv.no_load_store
        self.no_csr_instr = self.argv.no_csr_instr
        self.no_ebreak = self.argv.no_ebreak
        self.no_dret = self.argv.no_dret
        self.no_fence = self.argv.no_fence
        self.no_wfi = self.argv.no_wfi
        self.enable_unaligned_load_store = self.argv.enable_unaligned_load_store
        self.illegal_instr_ratio = self.argv.illegal_instr_ratio
        self.hint_instr_ratio = self.argv.hint_instr_ratio
        if self.argv.num_of_harts is None:
            self.num_of_harts = rcs.NUM_HARTS
        else:
            self.num_of_harts = self.argv.num_of_harts
        self.fix_sp = self.argv.fix_sp
        self.use_push_data_section = self.argv.use_push_data_section
        self.boot_mode_opts = self.argv.boot_mode
        # self.isa = self.argv.isa

        if self.boot_mode_opts:
            logging.info("Got boot mode option - %0s", self.boot_mode_opts)
            if self.boot_mode_opts == "m":
                self.init_privileged_mode = privileged_mode_t.MACHINE_MODE
            elif self.boot_mode_opts == "s":
                self.init_privileged_mode = privileged_mode_t.SUPERVISOR_MODE
            elif self.boot_mode_opts == "u":
                self.init_privileged_mode = privileged_mode_t.USER_MODE
            else:
                logging.error("Illegal boot mode option - %0s", self.boot_mode_opts)

        self.enable_page_table_exception = self.argv.enable_page_table_exception
        self.no_directed_instr = self.argv.no_directed_instr
        self.asm_test_suffix = self.argv.asm_test_suffix
        self.enable_interrupt = self.argv.enable_interrupt
        self.enable_nested_interrupt = self.argv.enable_nested_interrupt
        self.enable_timer_irq = self.argv.enable_timer_irq
        self.bare_program_mode = self.argv.bare_program_mode
        self.enable_illegal_csr_instruction = self.argv.enable_illegal_csr_instruction
        self.enable_access_invalid_csr_level = self.argv.enable_access_invalid_csr_level
        self.enable_misaligned_instr = self.argv.enable_misaligned_instr
        self.enable_dummy_csr_write = self.argv.enable_dummy_csr_write
        self.randomize_csr = self.argv.randomize_csr
        self.allow_sfence_exception = self.argv.allow_sfence_exception
        self.no_delegation = self.argv.no_delegation
        self.force_m_delegation = self.argv.force_m_delegation
        self.force_s_delegation = self.argv.force_s_delegation
        self.support_supervisor_mode = 0
        self.disable_compressed_instr = self.argv.disable_compressed_instr
        self.require_signature_addr = self.argv.require_signature_addr

        if self.require_signature_addr:
            self.signature_addr = int(self.argv.signature_addr, 16)
        else:
            self.signature_addr = 0xdeadbeef

        self.gen_debug_section = self.argv.gen_debug_section
        self.enable_ebreak_in_debug_rom = self.argv.enable_ebreak_in_debug_rom
        self.set_dcsr_ebreak = self.argv.set_dcsr_ebreak
        self.num_debug_sub_program = self.argv.num_debug_sub_program
        self.enable_debug_single_step = self.argv.enable_debug_single_step
        self.single_step_iterations = 0
        self.set_mstatus_tw = self.argv.set_mstatus_tw
        self.set_mstatus_mprv = vsc.bit_t(1)
        self.set_mstatus_mprv = self.argv.set_mstatus_mprv
        self.min_stack_len_per_program = 10 * (rcs.XLEN / 8)
        self.max_stack_len_per_program = 16 * (rcs.XLEN / 8)
        self.max_branch_step = 20
        self.reserved_regs = vsc.list_t(vsc.enum_t(riscv_reg_t))
        self.enable_floating_point = self.argv.enable_floating_point
        self.enable_vector_extension = self.argv.enable_vector_extension
        self.enable_b_extension = self.argv.enable_b_extension
        self.enable_bitmanip_groups = self.argv.enable_bitmanip_groups
        self.dist_control_mode = 0
        self.category_dist = {}
        self.march_isa = self.argv.march_isa

        if len(self.march_isa) != 0:
            rcs.supported_isa.append(self.march_isa)
        if riscv_instr_group_t.RV32C not in rcs.supported_isa:
            self.disable_compressed_instr = 1
        self.setup_instr_distribution()
        self.get_invalid_priv_lvl_csr()
        # Helpers fields to build the vsc constraints
        self.supported_interrupt_mode = vsc.list_t(vsc.enum_t(mtvec_mode_t))
        self.XLEN = vsc.uint32_t()
        self.SATP_MODE = vsc.enum_t(satp_mode_t)
        self.init_privil_mode = vsc.enum_t(privileged_mode_t)
        self.init_privil_mode = self.init_privileged_mode
        self.supported_interrupt_mode = rcs.supported_interrupt_mode
        self.XLEN = rcs.XLEN
        self.SATP_MODE = rcs.SATP_MODE
        self.tvec_ceil = vsc.uint32_t()
        self.tvec_ceil = math.ceil(math.log2((self.XLEN * 4) / 8))

    @vsc.constraint
    def default_c(self):
        self.main_program_instr_cnt in vsc.rangelist(vsc.rng(10, self.instr_cnt))

    @vsc.constraint
    def sp_tp_c(self):
        if self.fix_sp:
            self.sp == riscv_reg_t.SP
        self.sp != self.tp
        self.sp.not_inside(vsc.rangelist(riscv_reg_t.GP,
                                         riscv_reg_t.RA, riscv_reg_t.ZERO))
        self.tp.not_inside(vsc.rangelist(riscv_reg_t.GP,
                                         riscv_reg_t.RA, riscv_reg_t.ZERO))

    @vsc.constraint
    def gpr_c(self):
        with vsc.foreach(self.gpr, idx = True) as i:
            self.gpr[i].not_inside(vsc.rangelist(self.sp, self.tp, self.scratch_reg, self.pmp_reg,
                                                 riscv_reg_t.ZERO, riscv_reg_t.RA, riscv_reg_t.GP))
        vsc.unique(self.gpr)

    @vsc.constraint
    def ra_c(self):
        self.ra != riscv_reg_t.SP
        self.ra != riscv_reg_t.TP
        self.ra != riscv_reg_t.ZERO

    @vsc.constraint
    def reserve_scratch_reg_c(self):
        self.scratch_reg.not_inside(vsc.rangelist(riscv_reg_t.ZERO, self.sp,
                                                  self.tp, self.ra, riscv_reg_t.GP))

    @vsc.constraint
    def mtvec_c(self):
        self.mtvec_mode.inside(vsc.rangelist(self.supported_interrupt_mode))
        with vsc.if_then(self.mtvec_mode == mtvec_mode_t.DIRECT):
            vsc.soft(self.tvec_alignment == 2)
        with vsc.else_then():
            vsc.soft(self.tvec_alignment == self.tvec_ceil)

    @vsc.constraint
    def floating_point_c(self):
        with vsc.if_then(self.enable_floating_point):
            self.mstatus_fs == 1
        with vsc.else_then():
            self.mstatus_fs == 0

    @vsc.constraint
    def mstatus_c(self):
        with vsc.if_then(self.set_mstatus_mprv == 1):
            self.mstatus_mprv == 1
        with vsc.else_then():
            self.mstatus_mprv == 0
        with vsc.if_then(self.SATP_MODE == satp_mode_t.BARE):
            self.mstatus_mxr == 0
            self.mstatus_sum == 0
            self.mstatus_tvm == 0

    def check_setting(self):
        support_64b = 0
        support_128b = 0

        # check the valid isa support
        for group in rcs.supported_isa:
            if group in [riscv_instr_group_t.RV64I, riscv_instr_group_t.RV64M,
                         riscv_instr_group_t.RV64A, riscv_instr_group_t.RV64F,
                         riscv_instr_group_t.RV64D, riscv_instr_group_t.RV64C,
                         riscv_instr_group_t.RV64B]:
                support_64b = 1
                logging.info("support_64b = {}".format(support_64b))
                logging.debug("Supported ISA = {}".format(group.name))
            elif group in [riscv_instr_group_t.RV128I, riscv_instr_group_t.RV128C]:
                support_128b = 1
                logging.info("support_128b = {}".format(support_128b))
                logging.debug("Supported ISA = {}".format(group.name))

        if support_128b and rcs.XLEN != 128:
            logging.critical("XLEN should be set to 128 based on \
                              riscv_core_setting.supported_isa setting")
            logging.info("XLEN Value = {}".format(rcs.XLEN))
            sys.exit("XLEN is not equal to 128, set it Accordingly!")

        if not(support_128b) and support_64b and rcs.XLEN != 64:
            logging.critical("XLEN should be set to 64 based on \
                              riscv_core_setting.supported_isa setting")
            logging.info("XLEN Value = {}".format(rcs.XLEN))
            sys.exit("XLEN is not equal to 64, set it Accordingly!")

        if not(support_128b or support_64b) and rcs.XLEN != 32:
            logging.critical("XLEN should be set to 32 based on \
                              riscv_core_setting.supported_isa setting")
            logging.info("XLEN Value = {}".format(rcs.XLEN))
            sys.exit("XLEN is not equal to 32, set it Accordingly!")

        if not(support_128b or support_64b) and \
                not(rcs.SATP_MODE in [satp_mode_t.SV32, satp_mode_t.BARE]):
            logging.critical("SATP mode {} is not supported for RV32G ISA"
                             .format(rcs.SATP_MODE.name))
            sys.exit("Supported SATP mode is not provided")

    def setup_instr_distribution(self):
        if self.dist_control_mode:
            category_iter = iter([x for x in riscv_instr_category_t.__members__])
            category = riscv_instr_category_t(0)
            while True:
                opts = "dist_{}".format(category.name)
                opts = opts.lower()
                if self.args_dict[opts]:
                    self.category_dist[category] = self.args_dict[opts]
                else:
                    self.category_dist[category] = 10
                logging.info("Set dist[{}] = {}".format(category, self.category_dist[category]))
                category = next(category_iter)
                if category != riscv_instr_category_t(0):
                    break

    # TODO
    def init_delegation(self):
        pass

    def pre_randomize(self):
        for mode in rcs.supported_privileged_mode:
            if mode == privileged_mode_t.SUPERVISOR_MODE:
                self.support_supervisor_mode = 1

    def get_non_reserved_gpr(self):
        pass

    def post_randomize(self):
        self.reserved_regs.append(self.tp)
        self.reserved_regs.append(self.sp)
        self.reserved_regs.append(self.scratch_reg)
        self.min_stack_len_per_program = 2 * (rcs.XLEN / 8)
        logging.info("min_stack_len_per_program value = {}"
                     .format(self.min_stack_len_per_program))
        self.check_setting()  # check if the setting is legal

        if self.init_privileged_mode == privileged_mode_t.USER_MODE:
            logging.info("mode = USER_MODE")
            self.no_wfi = 1

    def get_invalid_priv_lvl_csr(self):
        invalid_lvl = []
        # Debug CSRs are inaccessible from all but Debug Mode
        # and we cannot boot into Debug Mode.
        invalid_lvl.append("D")
        if self.init_privileged_mode == privileged_mode_t.MACHINE_MODE:
            pass
        elif self.init_privileged_mode == privileged_mode_t.SUPERVISOR_MODE:
            invalid_lvl.append("M")
            logging.info("supr_mode---")
            logging.debug(invalid_lvl)
        elif self.init_privileged_mode == privileged_mode_t.USER_MODE:
            invalid_lvl.append("S")
            invalid_lvl.append("M")
            logging.info("usr_mode---")
            logging.debug(invalid_lvl)
        else:
            logging.critical("Unsupported initialization privilege mode")
            sys.exit(1)

        # implemented_csr from riscv_core_setting.py
        for csr in rcs.implemented_csr:
            if csr in invalid_lvl:
                self.invalid_priv_mode_csrs.append(csr)

    def parse_args(self):
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
        parse.add_argument('--num_of_sub_program', help = 'num_of_sub_program',
                           type = int, default = 5)
        parse.add_argument('--instr_cnt', help = 'instr_cnt', type = int, default = 200)
        parse.add_argument('--tvec_alignment', help = 'tvec_alignment', type = int, default = 2)
        parse.add_argument('--no_ebreak', help = 'no_ebreak',
                           choices = [0, 1], type = int, default = 1)
        parse.add_argument('--no_dret', help = 'no_dret', choices = [0, 1], type = int, default = 1)
        parse.add_argument('--no_wfi', help = 'no_wfi', choices = [0, 1], type = int, default = 1)

        parse.add_argument('--no_branch_jump', help = 'no_branch_jump',
                           choices = [0, 1], type = int, default = 0)
        parse.add_argument('--no_load_store', help = 'no_load_store',
                           choices = [0, 1], type = int, default = 0)
        parse.add_argument('--no_csr_instr', help = 'no_csr_instr',
                           choices = [0, 1], type = int, default = 0)
        parse.add_argument('--fix_sp', help = 'fix_sp',
                           choices = [0, 1], type = int, default = 0)
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
        parse.add_argument('--no_fence', help = 'no_fence',
                           choices = [0, 1], type = int, default = 1)
        parse.add_argument('--no_delegation', help = 'no_delegation',
                           choices = [0, 1], type = int, default = 1)
        parse.add_argument('--illegal_instr_ratio',
                           help = 'illegal_instr_ratio', type = int, default = 0)
        parse.add_argument('--hint_instr_ratio', help = 'hint_instr_ratio', type = int, default = 0)
        parse.add_argument('--num_of_harts', help = 'num_of_harts',
                           type = int, default = 1)
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
                           help = 'disable_compressed_instr', choices = [0, 1],
                           type = int, default = 0)
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
                           help = 'enable_debug_single_step', choices = [0, 1],
                           type = int, default = 0)
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
        parse.add_argument('--boot_mode', help = 'boot_mode', default = "")
        parse.add_argument('--asm_test_suffix', help = 'asm_test_suffix', default = "")
        parse.add_argument('--march_isa', help = 'march_isa', default = [],
                           choices = [i.name for i in riscv_instr_group_t], nargs = '*')
        for i in range(self.max_directed_instr_stream_seq):
            parse.add_argument('--directed_instr_{}'.format(i),
                               help = 'directed_instr_{}'.format(i), default = "")
            parse.add_argument('--stream_name_{}'.format(i),
                               help = 'stream_name_{}'.format(i), default = "")
            parse.add_argument('--stream_freq_{}'.format(i),
                               help = 'stream_freq_{}'.format(i), default = 4)
        parse.add_argument('--start_idx', help='start index', type=int, default=0)
        parse.add_argument('--asm_file_name', help='asm file name',
                           default="riscv_asm_test")
        parse.add_argument('--log_file_name', help='log file name',
                           default="")
        parse.add_argument('--target', help='target', default="rv32imc")
        parse.add_argument('--gen_test', help='gen_test', default="riscv_instr_base_test")
        parse.add_argument("--enable_visualization", action="store_true", default=False,
                           help="Enabling coverage report visualization for pyflow")
        parse.add_argument('--trace_csv', help='List of csv traces', default="")
        args, unknown = parse.parse_known_args()
        # TODO
        '''
        if ($value$plusargs("tvec_alignment=%0d", tvec_alignment)) begin
            tvec_alignment.rand_mode(0);
        end

        vector_cfg = riscv_vector_cfg::type_id::create("vector_cfg");
        pmp_cfg = riscv_pmp_cfg::type_id::create("pmp_cfg");
        pmp_cfg.rand_mode(pmp_cfg.pmp_randomize);
        pmp_cfg.initialize(require_signature_addr);
        setup_instr_distribution()
        get_invalid_priv_lvl_csr();
        '''
        args = parse.parse_args()

        return args


cfg = riscv_instr_gen_config()
