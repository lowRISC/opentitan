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
                                       mem_region_t, vreg_init_method_t)


# ----------------------------------------------------------------------------
# RISC-V assembly program generator configuration class
# ----------------------------------------------------------------------------

@vsc.randobj
class riscv_instr_gen_config:

    def __init__(self):
        # ---------------------------------------------------------------------------
        # Random instruction generation settings
        # ---------------------------------------------------------------------------

        # Instruction count of the main program
        self.main_program_instr_cnt = vsc.rand_int32_t()

        # Instruction count of each sub-program
        self.sub_program_instr_cnt = vsc.randsz_list_t(vsc.int32_t())

        # Instruction count of the debug rom
        self.debug_program_instr_cnt = 0

        # Instruction count of debug sub-programs
        self.debug_sub_program_instr_cnt = vsc.randsz_list_t(vsc.int32_t())

        # Pattern of data section: RAND_DATA, ALL_ZERO, INCR_VAL
        self.data_page_pattern = vsc.rand_enum_t(data_pattern_t)

        # Initialization of the vregs
        # SAME_VALUES_ALL_ELEMS - Using vmv.v.x to fill all the elements of the vreg with
        # the same value as the one in the GPR selected
        # RANDOM_VALUES_VMV     - Using vmv.v.x + vslide1up.vx to randomize the contents
        # of each vector element
        # RANDOM_VALUES_LOAD    - Using vle.v, same approach as RANDOM_VALUES_VMV but more
        # efficient for big VLEN
        self.vreg_init_method = vreg_init_method_t.RANDOM_VALUES_VMV

        # Maximum directed instruction stream sequence count
        self.max_directed_instr_stream_seq = 20

        self.init_delegation()
        self.argv = self.parse_args()
        self.args_dict = vars(self.argv)

        global rcs
        rcs = import_module("pygen_src.target." + self.argv.target + ".riscv_core_setting")

        # Dict for delegation configuration for each exception and interrupt
        # When the bit is 1, the corresponding delegation is enabled.
        # TODO
        self.m_mode_exception_delegation = {}
        self.s_mode_exception_delegation = {}
        self.m_mode_interrupt_delegation = {}
        self.s_mode_interrupt_delegation = {}

        # init_privileged_mode default to MACHINE_MODE
        # TODO: remove defult machine_mode once all modes get supported
        self.init_privileged_mode = privileged_mode_t.MACHINE_MODE

        self.mstatus = vsc.rand_bit_t(rcs.XLEN - 1)
        self.mie = vsc.rand_bit_t(rcs.XLEN - 1)
        self.sstatus = vsc.rand_bit_t(rcs.XLEN - 1)
        self.sie = vsc.rand_bit_t(rcs.XLEN - 1)
        self.ustatus = vsc.rand_bit_t(rcs.XLEN - 1)
        self.uie = vsc.rand_bit_t(rcs.XLEN - 1)

        # Key fields in xSTATUS
        # Memory protection bits
        self.mstatus_mprv = vsc.rand_bit_t(1)
        self.mstatus_mxr = vsc.rand_bit_t(1)
        self.mstatus_sum = vsc.rand_bit_t(1)
        self.mstatus_tvm = vsc.rand_bit_t(1)
        self.mstatus_fs = vsc.rand_bit_t(2)
        self.mstatus_vs = vsc.rand_bit_t(2)
        self.mtvec_mode = vsc.rand_enum_t(mtvec_mode_t)

        # TVEC alignment
        # This value is the log_2 of the byte-alignment of TVEC.BASE field
        # As per RISC-V privileged spec, default will be set to 2 (4-byte aligned)
        self.tvec_alignment = vsc.rand_uint32_t(self.argv.tvec_alignment)

        # Floating point rounding mode
        self.fcsr_rm = vsc.rand_enum_t(f_rounding_mode_t)

        # Enable sfence.vma instruction
        self.enable_sfence = vsc.rand_bit_t(1)

        # Reserved register
        # Reserved for various hardcoded routines
        self.gpr = vsc.rand_list_t(vsc.enum_t(riscv_reg_t), sz=4)

        # Used by any DCSR operations inside of the debug rom.
        # Also used by the PMP generation.
        self.scratch_reg = vsc.rand_enum_t(riscv_reg_t)

        # Reg used exclusively by the PMP exception handling routine.
        # Can overlap with the other GPRs used in the random generation,
        # as PMP exception handler is hardcoded and does not include any
        # random instructions.
        self.pmp_reg = vsc.rand_enum_t(riscv_reg_t)

        # Use a random register for stack pointer/thread pointer
        self.sp = vsc.rand_enum_t(riscv_reg_t)
        self.tp = vsc.rand_enum_t(riscv_reg_t)
        self.ra = vsc.rand_enum_t(riscv_reg_t)

        # Options for privileged mode CSR checking
        # Below checking can be made optional as the ISS implementation
        # could be different with the processor.
        self.check_misa_init_val = 0
        self.check_xstatus = 1

        # Virtual address translation is on for this test
        self.virtual_addr_translation_on = vsc.rand_bit_t(1)

        # Commenting out for now
        # vector_cfg = riscv_vector_cfg  # TODO
        # pmp_cfg = riscv_pmp_cfg  # TODO

        # Stack section word length
        self.stack_len = 5000

        # -----------------------------------------------------------------------------
        # User space memory region and stack setting
        # -----------------------------------------------------------------------------
        self.mem_region = vsc.list_t(mem_region_t())
        self.amo_region = vsc.list_t(mem_region_t())
        self.s_mem_region = vsc.list_t(mem_region_t())
        self.mem_region.extend([mem_region_t(name = "region_0", size_in_bytes = 4096, xwr = 8),
                                mem_region_t(name = "region_1", size_in_bytes = 4096, xwr = 8)])
        self.amo_region.extend([mem_region_t(name = "amo_0", size_in_bytes = 64, xwr = 8)])
        self.s_mem_region.extend([mem_region_t(name = "s_region_0", size_in_bytes = 4096, xwr = 8),
                                  mem_region_t(name = "s_region_1", size_in_bytes = 4096, xwr = 8)])
        # Kernel Stack section word length
        self.kernel_stack_len = 4000

        # Number of instructions for each kernel program
        self.kernel_program_instr_cnt = 400

        # List of all the main implemented CSRs that the boot privilege mode cannot access
        # e.g. these CSRs are in higher privilege modes - access should raise an exception
        self.invalid_priv_mode_csrs = []

        # -----------------------------------------------------------------------------
        # Command line options or control knobs
        # -----------------------------------------------------------------------------
        # Main options for RISC-V assembly program generation
        # Number of sub-programs per test
        self.num_of_sub_program = self.argv.num_of_sub_program
        self.instr_cnt = self.argv.instr_cnt
        self.num_of_tests = self.argv.num_of_tests
        # For tests doesn't involve load/store, the data section generation could be skipped
        self.no_data_page = self.argv.no_data_page
        # Options to turn off some specific types of instructions
        self.no_branch_jump = self.argv.no_branch_jump  # No branch/jump instruction
        self.no_load_store = self.argv.no_load_store  # No load/store instruction
        self.no_csr_instr = self.argv.no_csr_instr  # No csr instruction
        self.no_ebreak = self.argv.no_ebreak  # No ebreak instruction
        self.no_dret = self.argv.no_dret  # No dret instruction
        self.no_fence = self.argv.no_fence  # No fence instruction
        self.no_wfi = self.argv.no_wfi  # No WFI instruction
        self.enable_unaligned_load_store = self.argv.enable_unaligned_load_store
        self.illegal_instr_ratio = self.argv.illegal_instr_ratio
        self.hint_instr_ratio = self.argv.hint_instr_ratio
        # Number of harts to be simulated, must be <= NUM_HARTS
        if self.argv.num_of_harts is None:
            self.num_of_harts = rcs.NUM_HARTS
        else:
            self.num_of_harts = self.argv.num_of_harts
        # Use SP as stack pointer
        self.fix_sp = vsc.bit_t(1)
        self.fix_sp = self.argv.fix_sp
        # Use push/pop section for data pages
        self.use_push_data_section = self.argv.use_push_data_section
        # Directed boot privileged mode, u, m, s
        self.boot_mode_opts = self.argv.boot_mode
        # self.isa = self.argv.isa
        if self.boot_mode_opts:
            logging.info("Got boot mode option - {}".format(self.boot_mode_opts))
            if self.boot_mode_opts == "m":
                self.init_privileged_mode = privileged_mode_t.MACHINE_MODE
            elif self.boot_mode_opts == "s":
                self.init_privileged_mode = privileged_mode_t.SUPERVISOR_MODE
            elif self.boot_mode_opts == "u":
                self.init_privileged_mode = privileged_mode_t.USER_MODE
            else:
                logging.error("Illegal boot mode option - {}".format(self.boot_mode_opts))
        self.enable_page_table_exception = self.argv.enable_page_table_exception
        self.no_directed_instr = self.argv.no_directed_instr
        self.asm_test_suffix = self.argv.asm_test_suffix
        # Enable interrupt bit in MSTATUS (MIE, SIE, UIE)
        self.enable_interrupt = self.argv.enable_interrupt
        self.enable_nested_interrupt = self.argv.enable_nested_interrupt
        # We need a separate control knob for enabling timer interrupts, as Spike
        # throws an exception if xIE.xTIE is enabled
        self.enable_timer_irq = self.argv.enable_timer_irq
        # Generate a bare program without any init/exit/error handling/page table routines
        # The generated program can be integrated with a larger program.
        # Note that the bare mode program is not expected to run in standalone mode
        self.bare_program_mode = self.argv.bare_program_mode
        # Enable accessing illegal CSR instruction
        # - Accessing non-existence CSR
        # - Accessing CSR with wrong privileged mode
        self.enable_illegal_csr_instruction = self.argv.enable_illegal_csr_instruction
        # Enable accessing CSRs at an invalid privilege level
        self.enable_access_invalid_csr_level = self.argv.enable_access_invalid_csr_level
        # Enable misaligned instruction (caused by JALR instruction)
        self.enable_misaligned_instr = self.argv.enable_misaligned_instr
        # Enable some dummy writes to main system CSRs (xSTATUS/xIE) at beginning of test
        # to check repeated writes
        self.enable_dummy_csr_write = self.argv.enable_dummy_csr_write
        self.randomize_csr = self.argv.randomize_csr
        # sfence support
        self.allow_sfence_exception = self.argv.allow_sfence_exception
        # Interrupt/Exception Delegation
        self.no_delegation = self.argv.no_delegation
        self.force_m_delegation = self.argv.force_m_delegation
        self.force_s_delegation = self.argv.force_s_delegation
        self.support_supervisor_mode = 0  # TODO
        self.disable_compressed_instr = vsc.uint8_t(1)
        self.disable_compressed_instr = self.argv.disable_compressed_instr
        self.require_signature_addr = self.argv.require_signature_addr
        if self.require_signature_addr:
            self.signature_addr = int(self.argv.signature_addr, 16)
        else:
            self.signature_addr = 0xdeadbeef
        # Enable a full or empty debug_rom section.
        # Full debug_rom will contain random instruction streams.
        # Empty debug_rom will contain just dret instruction and will return immediately.
        # Will be empty by default.
        self.gen_debug_section = self.argv.gen_debug_section
        # Enable generation of a directed sequence of instructions containing
        # ebreak inside the debug_rom.
        # Disabled by default.
        self.enable_ebreak_in_debug_rom = self.argv.enable_ebreak_in_debug_rom
        # Enable setting dcsr.ebreak(m/s/u)
        self.set_dcsr_ebreak = self.argv.set_dcsr_ebreak
        # Number of sub programs in the debug rom
        self.num_debug_sub_program = self.argv.num_debug_sub_program
        # Enable debug single stepping
        self.enable_debug_single_step = self.argv.enable_debug_single_step
        # Number of single stepping iterations
        self.single_step_iterations = vsc.rand_uint32_t()
        # Enable mstatus.tw bit - causes u-mode WFI to raise illegal instruction exceptions
        self.set_mstatus_tw = self.argv.set_mstatus_tw
        # Enable users to set mstatus.mprv to enable privilege checks on memory accesses.
        self.set_mstatus_mprv = vsc.bit_t(1)
        self.set_mstatus_mprv = self.argv.set_mstatus_mprv
        # Stack space allocated to each program, need to be enough to store necessary context
        # Example: RA, SP, T0
        self.min_stack_len_per_program = 10 * (rcs.XLEN // 8)
        self.max_stack_len_per_program = 16 * (rcs.XLEN // 8)
        # Maximum branch distance, avoid skipping large portion of the code
        self.max_branch_step = 20
        # Reserved registers
        self.reserved_regs = vsc.list_t(vsc.enum_t(riscv_reg_t))
        # Floating point support
        self.enable_floating_point = vsc.bit_t(1)
        self.enable_floating_point = self.argv.enable_floating_point
        # Vector extension support
        self.enable_vector_extension = self.argv.enable_vector_extension
        # Only generate vector instructions
        self. vector_instr_only = vsc.bit_t(1)
        # Bit manipulation extension support
        self.enable_b_extension = self.argv.enable_b_extension
        self.enable_bitmanip_groups = self.argv.enable_bitmanip_groups

        # -----------------------------------------------------------------------------
        # Command line options for instruction distribution control
        # -----------------------------------------------------------------------------
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
        self.sub_program_instr_cnt.size == self.num_of_sub_program
        self.debug_sub_program_instr_cnt.size == self.num_debug_sub_program
        self.main_program_instr_cnt in vsc.rangelist(vsc.rng(10, self.instr_cnt))
        with vsc.foreach(self.sub_program_instr_cnt, idx=True) as i:
            self.sub_program_instr_cnt[i].inside(vsc.rangelist(vsc.rng(10, self.instr_cnt)))

    @vsc.constraint
    def debug_mode_c(self):
        # TODO
        pass

    # Keep the number of single step iterations relatively small
    @vsc.constraint
    def debug_single_step_c(self):
        # TODO
        pass

    # Boot privileged mode distribution
    @vsc.constraint
    def boot_privileged_mode_dist_c(self):
        # Boot to higher privileged mode more often
        # TODO
        pass

    @vsc.constraint
    def mtvec_c(self):
        self.mtvec_mode.inside(vsc.rangelist(self.supported_interrupt_mode))
        with vsc.if_then(self.mtvec_mode == mtvec_mode_t.DIRECT):
            vsc.soft(self.tvec_alignment == 2)
        with vsc.else_then():
            # Setting MODE = Vectored may impose an additional alignmentconstraint on BASE,
            # requiring up to 4×XLEN-byte alignment
            vsc.soft(self.tvec_alignment == self.tvec_ceil)

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

    # Exception delegation setting
    @vsc.constraint
    def exception_delegation_c(self):
        # Do not delegate instruction page fault to supervisor/user mode because this may introduce
        # dead loop. All the subsequent instruction fetches may fail and program cannot recover.
        # TODO
        pass

    # Spike only supports a subset of exception and interrupt delegation
    # You can modify this constraint if your ISS support different set of delegations
    @vsc.constraint
    def delegation_c(self):
        # TODO
        pass

    @vsc.constraint
    def ra_c(self):
        self.ra != riscv_reg_t.SP
        self.ra != riscv_reg_t.TP
        self.ra != riscv_reg_t.ZERO

    @vsc.constraint
    def sp_tp_c(self):
        with vsc.if_then(self.fix_sp == 1):
            self.sp == riscv_reg_t.SP
        self.sp != self.tp
        self.sp.not_inside(vsc.rangelist(riscv_reg_t.GP,
                                         riscv_reg_t.RA, riscv_reg_t.ZERO))
        self.tp.not_inside(vsc.rangelist(riscv_reg_t.GP,
                                         riscv_reg_t.RA, riscv_reg_t.ZERO))

    # This reg is used in various places throughout the generator,
    # so need more conservative constraints on it.
    @vsc.constraint
    def reserve_scratch_reg_c(self):
        self.scratch_reg.not_inside(vsc.rangelist(riscv_reg_t.ZERO, self.sp,
                                                  self.tp, self.ra, riscv_reg_t.GP))

    # This reg is only used inside PMP exception routine,
    # so we can be a bit looser with constraints.
    @vsc.constraint
    def reserved_pmp_reg_c(self):
        # TODO
        pass

    @vsc.constraint
    def gpr_c(self):
        with vsc.foreach(self.gpr, idx = True) as i:
            self.gpr[i].not_inside(vsc.rangelist(self.sp, self.tp, self.scratch_reg, self.pmp_reg,
                                                 riscv_reg_t.ZERO, riscv_reg_t.RA, riscv_reg_t.GP))
        vsc.unique(self.gpr)

    @vsc.constraint
    def addr_translation_rnd_order_c(self):
        # TODO
        pass

    @vsc.constraint
    def addr_translation_c(self):
        with vsc.if_then((self.init_privil_mode != privileged_mode_t.MACHINE_MODE) &
                         (self.SATP_MODE != satp_mode_t.BARE)):
            self.virtual_addr_translation_on == 1
        with vsc.else_then():
            self.virtual_addr_translation_on == 0

    @vsc.constraint
    def floating_point_c(self):
        with vsc.if_then(self.enable_floating_point == 1):
            self.mstatus_fs == 1
        with vsc.else_then():
            self.mstatus_fs == 0

    @vsc.constraint
    def mstatus_vs_c(self):
        # TODO
        pass

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
                    self.category_dist[category] = 10  # Default ratio
                logging.info("Set dist[{}] = {}".format(category, self.category_dist[category]))
                category = next(category_iter)
                if category != riscv_instr_category_t(0):
                    break

    # Initialize the exception/interrupt delegation associate array, set all delegation default to 0
    def init_delegation(self):
        # TODO
        pass

    def pre_randomize(self):
        for mode in rcs.supported_privileged_mode:
            if mode == privileged_mode_t.SUPERVISOR_MODE:
                self.support_supervisor_mode = 1

    def get_non_reserved_gpr(self):
        pass

    def post_randomize(self):
        # Setup the list all reserved registers
        self.reserved_regs.extend((self.tp, self.sp, self.scratch_reg))
        # Need to save all loop registers, and RA/T0
        self.min_stack_len_per_program = 2 * (rcs.XLEN // 8)
        logging.info("min_stack_len_per_program value = {}"
                     .format(self.min_stack_len_per_program))
        self.check_setting()  # check if the setting is legal
        # WFI is not supported in umode
        if self.init_privileged_mode == privileged_mode_t.USER_MODE:
            self.no_wfi = 1

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

    # Populate invalid_priv_mode_csrs with the main implemented CSRs for each supported privilege
    # mode
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
                           type = int)
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
        parse.add_argument('--seed', help='Seed value', default=None)
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
