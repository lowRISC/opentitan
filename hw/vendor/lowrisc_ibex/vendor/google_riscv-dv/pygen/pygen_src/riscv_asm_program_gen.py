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

import logging
import random
import copy
import sys
import vsc
from importlib import import_module
from pygen_src.riscv_instr_sequence import riscv_instr_sequence
from pygen_src.riscv_callstack_gen import riscv_callstack_gen
from pygen_src.riscv_instr_pkg import (pkg_ins, privileged_reg_t,
                                       privileged_mode_t, mtvec_mode_t,
                                       misa_ext_t, riscv_instr_group_t,
                                       satp_mode_t, exception_cause_t)
from pygen_src.riscv_signature_pkg import (signature_type_t, core_status_t,
                                           test_result_t)
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_data_page_gen import riscv_data_page_gen
from pygen_src.riscv_privileged_common_seq import riscv_privileged_common_seq
from pygen_src.riscv_utils import factory
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


# ----------------------------------------------------------------------------------
# RISC-V assembly program generator

# This is the main class to generate a complete RISC-V program, including the init routine,
# instruction section, data section, stack section, page table, interrupt and exception
# handling etc. Check gen_program() function to see how the program is generated.
# ----------------------------------------------------------------------------------


@vsc.randobj
class riscv_asm_program_gen:

    def __init__(self):
        self.instr_stream = []
        # Directed instruction ratio, occurance per 1000 instructions
        self.directed_instr_stream_ratio = {}
        self.hart = 0
        self.page_table_list = []
        self.main_program = []
        self.sub_program = [0] * rcs.NUM_HARTS
        self.data_page_gen = None
        self.spf_val = vsc.rand_bit_t(32)
        self.dpf_val = vsc.rand_bit_t(64)

    # ----------------------------------------------------------------------------------
    # Main function to generate the whole program
    # ----------------------------------------------------------------------------------

    # This is the main function to generate all sections of the program.
    def gen_program(self):
        self.instr_stream.clear()
        # Generate program header
        self.gen_program_header()
        for hart in range(cfg.num_of_harts):
            sub_program_name = []
            self.instr_stream.append(f"h{int(hart)}_start:")
            if not cfg.bare_program_mode:
                self.setup_misa()
                # Create all page tables
                self.create_page_table(hart)
                # Setup privileged mode registers and enter target privileged mode
                self.pre_enter_privileged_mode(hart)
            # Init section
            self.gen_init_section(hart)
            '''
            If PMP is supported, we want to generate the associated trap handlers and the test_done
            section at the start of the program so we can allow access through the pmpcfg0 CSR
            '''
            if(rcs.support_pmp and not(cfg.bare_program_mode)):
                self.gen_trap_handlers(hart)
                # Ecall handler
                self.gen_ecall_handler(hart)
                # Instruction fault handler
                self.gen_instr_fault_handler(hart)
                # Load fault handler
                self.gen_load_fault_handler(hart)
                # Store fault handler
                self.gen_store_fault_handler(hart)
                if hart == 0:
                    self.gen_test_done()
            # Generate sub program
            self.gen_sub_program(hart, self.sub_program[hart],
                                 sub_program_name, cfg.num_of_sub_program)
            # Generate main program
            gt_lbl_str = pkg_ins.get_label("main", hart)
            label_name = gt_lbl_str
            gt_lbl_str = riscv_instr_sequence()
            self.main_program.append(gt_lbl_str)
            self.main_program[hart].instr_cnt = cfg.main_program_instr_cnt
            self.main_program[hart].is_debug_program = 0
            self.main_program[hart].label_name = label_name
            self.generate_directed_instr_stream(hart=hart,
                                                label=self.main_program[hart].label_name,
                                                original_instr_cnt=
                                                self.main_program[hart].instr_cnt,
                                                min_insert_cnt=1,
                                                instr_stream=self.main_program[hart].directed_instr)
            self.main_program[hart].gen_instr(is_main_program=1, no_branch=cfg.no_branch_jump)
            # Setup jump instruction among main program and sub programs
            self.gen_callstack(self.main_program[hart], self.sub_program[hart],
                               sub_program_name, cfg.num_of_sub_program)
            self.main_program[hart].post_process_instr()
            logging.info("Post-processing main program...done")
            self.main_program[hart].generate_instr_stream()
            logging.info("Generating main program instruction stream...done")
            self.instr_stream.extend(self.main_program[hart].instr_string_list)
            """
            If PMP is supported, need to jump from end of main program
            to test_done section at the end of main_program, as the test_done
            will have moved to the beginning of the program
            """
            self.instr_stream.extend(("{}la x{}, test_done".format(pkg_ins.indent, cfg.scratch_reg),
                                      "{}jalr x0, x{}, 0".format(pkg_ins.indent, cfg.scratch_reg)))
            # Test done section
            # If PMP isn't supported, generate this in the normal location
            if(hart == 0 and not(rcs.support_pmp)):
                self.gen_test_done()
            # Shuffle the sub programs and insert to the instruction stream
            self.insert_sub_program(self.sub_program[hart], self.instr_stream)
            logging.info("Main/sub program generation...done")
            # program end
            self.gen_program_end(hart)
            if not cfg.bare_program_mode:
                # Generate debug rom section
                if rcs.support_debug_mode:
                    self.gen_debug_rom(hart)
                self.gen_section(pkg_ins.hart_prefix(hart) + "instr_end", ["nop"])
        for hart in range(cfg.num_of_harts):
            # Starting point of data section
            self.gen_data_page_begin(hart)
            if not cfg.no_data_page:
                # User data section
                self.gen_data_page(hart)
                # AMO memory region
                if(hart == 0 and riscv_instr_group_t.RV32A in rcs.supported_isa):
                    self.gen_data_page(hart, amo = 1)
            # Stack section
            self.gen_stack_section(hart)
            if not cfg.bare_program_mode:
                # Generate kernel program/data/stack section
                self.gen_kernel_sections(hart)
                # Page table
                self.gen_page_table_section(hart)

    # ----------------------------------------------------------------------------------
    # Generate kernel program/data/stack sections
    # ----------------------------------------------------------------------------------

    def gen_kernel_sections(self, hart):
        if rcs.SATP_MODE != satp_mode_t.BARE:
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")
        self.instr_stream.append(pkg_ins.get_label("kernel_instr_start:", hart))
        self.instr_stream.append(".text")
        # Kernel programs
        # TODO

        # All trap/interrupt handling is in the kernel region
        # Trap/interrupt delegation to user mode is not supported now
        # Trap handler
        self.gen_all_trap_handler(hart)
        # Interrupt handling subroutine
        for mode in rcs.supported_privileged_mode:
            self.gen_interrupt_handler_section(mode, hart)
        self.instr_stream.append(pkg_ins.get_label("kernel_instr_end: nop", hart))
        # User stack and data pages may not be accessible when executing trap handling programs in
        # machine/supervisor mode. Generate separate kernel data/stack sections to solve it.
        if not cfg.virtual_addr_translation_on:
            if rcs.SATP_MODE != satp_mode_t.BARE:
                self.instr_stream.append(".align 12")
            else:
                self.instr_stream.append(".align 2")
            # Kernel data pages
            self.instr_stream.append(pkg_ins.get_label("kernel_data_start:", hart))
            if not cfg.no_data_page:
                # Data section
                self.gen_data_page(hart, 1)
        # Kernel stack section
        self.gen_kernel_stack_section(hart)

    def gen_kernel_program(self, hart, seq):
        # TODO
        pass

    # ----------------------------------------------------------------------------------
    # Generate any subprograms and set up the callstack
    # ----------------------------------------------------------------------------------

    def gen_sub_program(self, hart, sub_program,
                        sub_program_name, num_sub_program,
                        is_debug = 0, prefix = "sub"):
        if num_sub_program > 0:
            self.sub_program = [0] * num_sub_program
            for i in range(len(self.sub_program)):
                gt_label_str = pkg_ins.get_label("{}_{}".format(prefix, i + 1), hart)
                label_name = gt_label_str
                gt_label_str = riscv_instr_sequence()
                self.sub_program[i] = gt_label_str
                if(is_debug):
                    self.sub_program[i].instr_cnt = cfg.debug_sub_program_instr_cnt[i]
                else:
                    self.sub_program[i].instr_cnt = cfg.sub_program_instr_cnt[i]
                self.generate_directed_instr_stream(hart=hart,
                                                    label=label_name,
                                                    original_instr_cnt=
                                                    self.sub_program[i].instr_cnt,
                                                    min_insert_cnt=0,
                                                    instr_stream=self.sub_program[i].directed_instr)
                self.sub_program[i].label_name = label_name
                self.sub_program[i].gen_instr(is_main_program=0, no_branch=cfg.no_branch_jump)
                sub_program_name.append(self.sub_program[i].label_name)

    def gen_callstack(self, main_program, sub_program,
                      sub_program_name, num_sub_program):
        if num_sub_program != 0:
            callstack_gen = riscv_callstack_gen()
            self.callstack_gen.init(num_sub_program + 1)
            if callstack_gen.randomize():
                idx = 0
                # Insert the jump instruction based on the call stack
                for i in range(len(callstack_gen.program_h)):
                    for j in range(len(callstack_gen.program_h.sub_program_id)):
                        idx += 1
                        pid = callstack_gen.program_id[i].sub_program_id[j] - 1
                        logging.info("Gen jump instr %0s -> sub[%0d] %0d", i, j, pid + 1)
                        if(i == 0):
                            self.main_program[i].insert_jump_instr(sub_program_name[pid], idx)
                        else:
                            self.sub_program[i - 1].insert_jump_instr(sub_program_name[pid], idx)
            else:
                logging.critical("Failed to generate callstack")
                sys.exit(1)
        logging.info("Randomizing call stack..done")

    def insert_sub_program(self, sub_program, instr_list):
        if cfg.num_of_sub_program != 0:
            random.shuffle(self.sub_program)
            for i in range(len(self.sub_program)):
                self.sub_program[i].post_process_instr()
                self.sub_program[i].generate_instr_stream()
                instr_list.extend((self.sub_program[i].instr_string_list))

    # ----------------------------------------------------------------------------------
    # Major sections - init, stack, data, test_done etc.
    # ----------------------------------------------------------------------------------

    def gen_program_header(self):
        header_string = []
        self.instr_stream.extend((".include \"user_define.h\"", ".globl _start", ".section .text"))
        if cfg.disable_compressed_instr:
            self.instr_stream.append(".option norvc;")
        header_string.extend((".include \"user_init.s\"",
                              "csrr x5, {}".format(hex(privileged_reg_t.MHARTID))))
        for hart in range(cfg.num_of_harts):
            header_string.extend(("li x6, {}".format(hart),
                                  "beq x5, x6, {}f".format(hart)))
        self.gen_section("_start", header_string)
        for hart in range(cfg.num_of_harts):
            self.instr_stream.extend(("{}: la x{}, h{}_start".format(hart, cfg.scratch_reg, hart),
                                      "jalr x0, x{}, 0".format(cfg.scratch_reg)))

    def gen_program_end(self, hart):
        if hart == 0:
            # Use write_tohost to terminate spike simulation
            self.gen_section("write_tohost", ["sw gp, tohost, t5"])
            self.gen_section("_exit", ["j write_tohost"])

    def gen_data_page_begin(self, hart):
        self.instr_stream.append(".section .data")
        if hart == 0:
            self.instr_stream.extend((".align 6; .global tohost; tohost: .dword 0;",
                                      ".align 6; .global fromhost; fromhost: .dword 0;"))

    def gen_data_page(self, hart, is_kernel = 0, amo = 0):
        self.data_page_gen = riscv_data_page_gen()
        self.data_page_gen.gen_data_page(hart, cfg.data_page_pattern, is_kernel, amo)
        self.instr_stream.extend(self.data_page_gen.data_page_str)

    def gen_stack_section(self, hart):
        hart_prefix_string = pkg_ins.hart_prefix(hart)
        if cfg.use_push_data_section:
            self.instr_stream.append(
                ".pushsection .{}user_stack,\"aw\",@progbits;".format(hart_prefix_string))
        else:
            self.instr_stream.append(
                ".section .{}user_stack,\"aw\",@progbits;".format(hart_prefix_string))
        if rcs.SATP_MODE != satp_mode_t.BARE:
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")

        self.instr_stream.extend((pkg_ins.get_label("user_stack_start:", hart),
                                  ".rept {}".format(cfg.stack_len - 1),
                                  ".{}byte 0x0".format(rcs.XLEN // 8), ".endr",
                                  pkg_ins.get_label("user_stack_end:", hart),
                                  ".{}byte 0x0".format(rcs.XLEN // 8)))
        if cfg.use_push_data_section:
            self.instr_stream.append(".popsection;")

    # The kernal stack is used to save user program context before executing exception handling
    def gen_kernel_stack_section(self, hart):
        hart_prefix_string = pkg_ins.hart_prefix(hart)
        if cfg.use_push_data_section:
            self.instr_stream.append(
                ".pushsection .{}kernel_stack,\"aw\",@progbits;".format(hart_prefix_string))
        else:
            self.instr_stream.append(
                ".section .{}kernel_stack,\"aw\",@progbits;".format(hart_prefix_string))
        if rcs.SATP_MODE != satp_mode_t.BARE:
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")
        self.instr_stream.extend((pkg_ins.get_label("kernel_stack_start:", hart),
                                  ".rept {}".format(cfg.stack_len - 1),
                                  ".{}byte 0x0".format(rcs.XLEN // 8), ".endr",
                                  pkg_ins.get_label("kernel_stack_end:", hart),
                                  ".{}byte 0x0".format(rcs.XLEN // 8)))
        if cfg.use_push_data_section:
            self.instr_stream.append(".popsection;")

    def gen_init_section(self, hart):
        init_string = pkg_ins.format_string(pkg_ins.get_label("init:", hart), pkg_ins.LABEL_STR_LEN)
        self.instr_stream.append(init_string)
        if cfg.enable_floating_point:
            self.init_floating_point_gpr()
        self.init_gpr()
        # Init stack pointer to point to the end of the user stack
        init_string = "{}la x{}, {}user_stack_end".format(
            pkg_ins.indent, cfg.sp, pkg_ins.hart_prefix(hart))
        self.instr_stream.append(init_string)
        if cfg.enable_vector_extension:
            self.randomize_vec_gpr_and_csr()
        self.core_is_initialized()
        self.gen_dummy_csr_write()
        if rcs.support_pmp:
            init_string = pkg_ins.indent + "j main"
            self.instr_stream.append(init_string)

    # Setup MISA based on supported extensions
    def setup_misa(self):
        misa = vsc.bit_t(rcs.XLEN)
        if rcs.XLEN == 32:
            misa[rcs.XLEN - 1:rcs.XLEN - 2] = 1
        elif rcs.XLEN == 64:
            misa[rcs.XLEN - 1:rcs.XLEN - 2] = 2
        else:
            misa[rcs.XLEN - 1:rcs.XLEN - 2] = 3
        if cfg.check_misa_init_val:
            self.instr_stream.append("{}csrr x15, {}".format(pkg_ins.indent,
                                                             hex(privileged_reg_t.MISA)))
        for group in rcs.supported_isa:
            if group in [riscv_instr_group_t.RV32C,
                         riscv_instr_group_t.RV64C,
                         riscv_instr_group_t.RV128C]:
                misa[misa_ext_t.MISA_EXT_C] = 1
            elif group in [riscv_instr_group_t.RV32I,
                           riscv_instr_group_t.RV64I,
                           riscv_instr_group_t.RV128I]:
                misa[misa_ext_t.MISA_EXT_I] = 1
            elif group in [riscv_instr_group_t.RV32M,
                           riscv_instr_group_t.RV64M]:
                misa[misa_ext_t.MISA_EXT_M] = 1
            elif group in [riscv_instr_group_t.RV32A,
                           riscv_instr_group_t.RV64A]:
                misa[misa_ext_t.MISA_EXT_A] = 1
            elif group in [riscv_instr_group_t.RV32B,
                           riscv_instr_group_t.RV64B]:
                misa[misa_ext_t.MISA_EXT_B] = 1
            elif group in [riscv_instr_group_t.RV32F,
                           riscv_instr_group_t.RV64F,
                           riscv_instr_group_t.RV32FC]:
                misa[misa_ext_t.MISA_EXT_F] = 1
            elif group in [riscv_instr_group_t.RV32D,
                           riscv_instr_group_t.RV64D,
                           riscv_instr_group_t.RV32DC]:
                misa[misa_ext_t.MISA_EXT_D] = 1
            elif group in [riscv_instr_group_t.RVV]:
                misa[misa_ext_t.MISA_EXT_V] = 1
            elif group in [riscv_instr_group_t.RV32X,
                           riscv_instr_group_t.RV64X]:
                misa[misa_ext_t.MISA_EXT_X] = 1
            else:
                logging.critical("{} is not yet supported".format(group.name))
                sys.exit(1)
        if privileged_mode_t.SUPERVISOR_MODE in rcs.supported_privileged_mode:
            misa[misa_ext_t.MISA_EXT_S] = 1
        self.instr_stream.extend(("{}li x{}, {}".format(pkg_ins.indent, cfg.gpr[0],
                                                        hex(misa.get_val())),
                                  "{}csrw {}, x{}".format(pkg_ins.indent,
                                                          hex(privileged_reg_t.MISA), cfg.gpr[0])))

    # Write to the signature_addr with values to indicate to the core testbench
    # that is safe to start sending interrupt and debug stimulus
    def core_is_initialized(self):
        instr = []
        if cfg.require_signature_addr:
            if cfg.signature_addr != 0xdeadbeef:
                self.gen_signature_handshake(instr, signature_type_t.CORE_STATUS,
                                             core_status_t.INITIALIZED)
                self.format_section(instr)
                self.instr_stream.append(instr)
            else:
                logging.critical("The signature_addr is not properly configured!")
                sys.exit(1)

    # Generate some dummy writes to xSTATUS/xIE at the beginning of the test to check
    # repeated writes to these CSRs.
    def gen_dummy_csr_write(self):
        # TODO
        pass

    # Initialize general purpose registers with random value
    def init_gpr(self):
        reg_val = vsc.rand_bit_t(pkg_ins.DATA_WIDTH)
        # Init general purpose registers with random values
        for i in range(rcs.NUM_GPR):
            if i in [cfg.sp.value, cfg.tp.value]:
                continue
            try:
                with vsc.randomize_with(reg_val):
                    vsc.dist(reg_val, [vsc.weight(0, 1), vsc.weight(0x80000000, 1),
                                       vsc.weight(vsc.rng(0x1, 0xf), 1),
                                       vsc.weight(vsc.rng(0x10, 0xefffffff), 1),
                                       vsc.weight(vsc.rng(0xf0000000, 0xffffffff), 1)])
            except Exception:
                logging.critical("Cannot Randomize reg_val")
                sys.exit(1)
            self.instr_stream.append("{}li x{}, {}".format(pkg_ins.indent, i,
                                                           hex(reg_val.get_val())))

    # Initialize vector general purpose registers
    def init_vec_gpr(self):
        # TODO
        pass

    # Initialize floating point general purpose registers
    def init_floating_point_gpr(self):
        for i in range(rcs.NUM_FLOAT_GPR):
            vsc.randselect([
                (1, lambda: self.init_floating_point_gpr_with_spf(i)),
                (riscv_instr_group_t.RV64D in rcs.supported_isa,
                 lambda: self.init_floating_point_gpr_with_dpf(i))])
        # Initialize rounding mode of FCSR and append to the instr_stream
        self.instr_stream.append("{}fsrmi {}".format(pkg_ins.indent, cfg.fcsr_rm))

    # get instructions initialize floating_point_gpr with single precision floating value
    def init_floating_point_gpr_with_spf(self, int_floating_gpr):
        imm = self.get_rand_spf_value()
        li_instr = "{}li x{}, {}".format(pkg_ins.indent, cfg.gpr[0], hex(imm))
        fmv_instr = "{}fmv.w.x f{}, x{}".format(pkg_ins.indent, int_floating_gpr,
                                                cfg.gpr[0])
        self.instr_stream.extend((li_instr, fmv_instr))

    # get instructions initialize floating_point_gpr with double precision floating value
    def init_floating_point_gpr_with_dpf(self, int_floating_gpr):
        imm = vsc.bit_t(64)
        imm = self.get_rand_dpf_value()
        int_gpr1 = cfg.gpr[0].value
        int_gpr2 = cfg.gpr[1].value

        li_instr0 = "{}li x{}, {}".format(pkg_ins.indent, int_gpr1, imm[63:32])
        # shift to upper 32bits
        for _ in range(2):
            slli_instr = "{}slli x{}, x{}, 16".format(pkg_ins.indent, int_gpr1, int_gpr1)
        li_instr1 = "{}li x{}, {}".format(pkg_ins.indent, int_gpr2, imm[31:0])
        or_instr = "{}or x{}, x{}, x{}".format(pkg_ins.indent, int_gpr2, int_gpr2, int_gpr1)
        fmv_instr = "{}fmv.d.x f{}, x{}".format(pkg_ins.indent, int_floating_gpr, int_gpr2)
        self.instr_stream.extend((li_instr0, slli_instr, li_instr1, or_instr, fmv_instr))

    def get_randselect(self, addr_range1, addr_range2, flag):
        if flag:
            # Get a random double precision floating value
            with vsc.raw_mode():
                with vsc.randomize_with(self.dpf_val):
                    self.dpf_val in vsc.rangelist(addr_range1, addr_range2)
        else:
            # Get a random single precision floating value
            with vsc.raw_mode():
                with vsc.randomize_with(self.spf_val):
                    self.spf_val in vsc.rangelist(addr_range1, addr_range2)

    def get_rng(self, val0, val1, spf_dpf, flag):
        if flag == 0 and spf_dpf == 32:
            with vsc.raw_mode():
                with vsc.randomize_with(self.spf_val):
                    self.spf_val[val0:val1] > 0
        elif flag == 0 and spf_dpf == 64:
            with vsc.raw_mode():
                with vsc.randomize_with(self.dpf_val):
                    self.dpf_val[val0:val1] > 0
        elif flag == 1 and spf_dpf == 32:
            with vsc.raw_mode():
                with vsc.randomize_with(self.spf_val):
                    self.spf_val[val0:val1] == 0
        else:
            with vsc.raw_mode():
                with vsc.randomize_with(self.dpf_val):
                    self.dpf_val[val0:val1] == 0

    def get_rand_spf_value(self):
        vsc.randselect([
            # Infinity
            (1, lambda: self.get_randselect(0x7f80_0000, 0xff80_0000, 0)),
            # Largest
            (1, lambda: self.get_randselect(0x7f7f_ffff, 0xff7f_ffff, 0)),
            # Zero
            (1, lambda: self.get_randselect(0x0000_0000, 0x8000_0000, 0)),
            # NaN
            (1, lambda: self.get_randselect(0x7f80_0001, 0x7fc0_0000, 0)),
            # Normal
            (1, lambda: self.get_rng(30, pkg_ins.SINGLE_PRECISION_FRACTION_BITS, 32, 0)),
            # Subnormal
            (1, lambda: self.get_rng(30, pkg_ins.SINGLE_PRECISION_FRACTION_BITS, 32, 1))])
        return self.spf_val

    def get_rand_dpf_value(self):
        vsc.randselect([
            # Infinity
            (1, lambda: self.get_randselect(0x7ff0_0000_0000_0000, 0xfff0_0000_0000_0000, 1)),
            # largest
            (1, lambda: self.get_randselect(0x7fef_ffff_ffff_ffff, 0xffef_ffff_ffff_ffff, 1)),
            # Zero
            (1, lambda: self.get_randselect(0x0000_0000_0000_0000, 0x8000_0000_0000_0000, 1)),
            # NaN
            (1, lambda: self.get_randselect(0x7ff0_0000_0000_0001, 0x7ff8_0000_0000_0000, 1)),
            # Normal
            (1, lambda: self.get_rng(62, pkg_ins.DOUBLE_PRECISION_FRACTION_BITS, 64, 0)),
            # Subnormal
            (1, lambda: self.get_rng(62, pkg_ins.DOUBLE_PRECISION_FRACTION_BITS, 64, 1))])
        return self.dpf_val

    # Generate "test_done" section, test is finished by an ECALL instruction
    # The ECALL trap handler will handle the clean up procedure before finishing the test.

    def gen_test_done(self):
        self.instr_stream.extend((pkg_ins.format_string("test_done:", pkg_ins.LABEL_STR_LEN),
                                  pkg_ins.indent + "li gp, 1"))
        if cfg.bare_program_mode:
            self.instr_stream.append(pkg_ins.indent + "j write_tohost")
        else:
            self.instr_stream.append(pkg_ins.indent + "ecall")

    # Dump all GPR to the starting point of the program
    # TB can check the GPR value for this memory location to compare with expected value generated
    # by the ISA simulator. If the processor doesn't have a good tracer unit, it might not be
    # possible to compare the GPR value after each instruction execution.
    def gen_register_dump(self, instr):
        # load base address
        instr.append("la x{}, _start".format(cfg.gpr[0]))
        # Generate sw/sd instructions
        for i in range(32):
            if rcs.XLEN == 64:
                dump_str = "sd x{}, {}(x{})".format(i, i * (rcs.XLEN // 8), cfg.gpr[0])
            else:
                dump_str = "sw x{}, {}(x{})".format(i, i * (rcs.XLEN // 8), cfg.gpr[0])
            instr.append(dump_str)

    # ----------------------------------------------------------------------------------
    # Privileged mode entering routine
    # ----------------------------------------------------------------------------------

    def pre_enter_privileged_mode(self, hart):
        instr = []
        privil_str = []
        # Setup kernel stack pointer
        privil_str.append("la x{}, {}kernel_stack_end".format(cfg.tp, pkg_ins.hart_prefix(hart)))
        self.gen_section(pkg_ins.get_label("kernel_sp", hart), privil_str)
        # Setup interrupt and exception delegation
        if not cfg.no_delegation and (cfg.init_privileged_mode != privileged_mode_t.MACHINE_MODE):
            self.gen_delegation(hart)
        # Setup trap vector register
        self.trap_vector_init(hart)
        # Setup PMP CSRs
        self.setup_pmp(hart)
        # Generate PMPADDR write test sequence
        self.gen_pmp_csr_write(hart)
        # Initialize PTE (link page table based on their real physical address)
        if cfg.virtual_addr_translation_on:
            # TODO
            # self.page_table_list.process_page_table(instr)
            self.gen_section(pkg_ins.get_label("process_pt", hart), instr)
        # Setup mepc register, jump to init entry
        self.setup_epc(hart)
        # Initialization of any implementation-specific custom CSRs
        self.setup_custom_csrs(hart)
        # Setup initial privilege mode
        self.gen_privileged_mode_switch_routine(hart)

    def gen_privileged_mode_switch_routine(self, hart):
        privil_seq = riscv_privileged_common_seq()
        for privil_mode in rcs.supported_privileged_mode:
            instr = []
            # csr_handshake = []
            if privil_mode != cfg.init_privileged_mode:
                continue
            logging.info("Generating privileged mode routing for {}"
                         .format(privil_mode.name))
            # Enter Privileged mode
            privil_seq.hart = hart
            privil_seq.randomize()
            privil_seq.enter_privileged_mode(privil_mode, instr)
            if cfg.require_signature_addr:
                # TODO
                pass
        self.instr_stream.extend(instr)

    # Setup EPC before entering target privileged mode
    def setup_epc(self, hart):
        instr = []
        instr.append("la x{}, {}init".format(cfg.gpr[0], pkg_ins.hart_prefix(hart)))

        if cfg.virtual_addr_translation_on:
            # For supervisor and user mode, use virtual address instead of physical address.
            # Virtual address starts from address 0x0, here only the lower 12 bits are kept
            # as virtual address offset.
            instr.extend(("slli x{}, x{}, {}".format(cfg.gpr[0], cfg.gpr[0], rcs.XLEN - 12),
                          "srli x{}, x{}, {}".format(cfg.gpr[0], cfg.gpr[0], rcs.XLEN - 12)))
        instr.append("csrw {}, x{}".format(hex(privileged_reg_t.MEPC), cfg.gpr[0]))
        self.gen_section(pkg_ins.get_label("mepc_setup", hart), instr)

    # Setup PMP CSR configuration
    def setup_pmp(self, hart):
        # TODO
        pass
    # Generates a directed stream of instructions to write random values to all supported
    # pmpaddr CSRs to test write accessibility.
    # The original CSR values are restored afterwards.

    def gen_pmp_csr_write(self, hart):
        # TODO
        pass

    # Handles creation of a subroutine to initialize any custom CSRs
    def setup_custom_csrs(self, hart):
        # TODO
        pass

    # This function should be overridden in the riscv_asm_program_gen extended class
    # corresponding to the RTL implementation if it has any custom CSRs defined.

    # All that needs to be done in the overridden function is to manually create
    # the instruction strings to set up any custom CSRs and then to push those strings
    # into the instr queue.
    def init_custom_csr(self, instr):
        # TODO
        pass

    # ---------------------------------------------------------------------------------------
    # Privileged CSR setup for interrupt and exception handling and delegation
    # ---------------------------------------------------------------------------------------

    # Interrupt and exception delegation setting.
    # The lower level exception and interrupt can be delegated to higher level handler.
    def gen_delegation(self, hart):
        self.gen_delegation_instr(hart,
                                  privileged_reg_t.MEDELEG,
                                  privileged_reg_t.MIDELEG,
                                  cfg.m_mode_exception_delegation,
                                  cfg.m_mode_interrupt_delegation)
        if rcs.support_umode_trap:
            self.gen_delegation_instr(hart,
                                      privileged_reg_t.SEDELEG,
                                      privileged_reg_t.SIDELEG,
                                      cfg.s_mode_exception_delegation,
                                      cfg.s_mode_interrupt_delegation)

    def gen_delegation_instr(self, hart, edeleg, ideleg,
                             edeleg_enable, ideleg_enable):
        # TODO
        pass

    # Setup trap vector - MTVEC, STVEC, UTVEC
    def trap_vector_init(self, hart):
        instr = []
        for mode in rcs.supported_privileged_mode:
            if mode == privileged_mode_t.MACHINE_MODE:
                trap_vec_reg = privileged_reg_t.MTVEC
            elif mode == privileged_mode_t.SUPERVISOR_MODE:
                trap_vec_reg = privileged_reg_t.STVEC
            elif mode == privileged_mode_t.USER_MODE:
                trap_vec_reg = privileged_reg_t.UTVEC
            else:
                logging.critical("Unsupported privileged_mode {}".format(mode.name))
                sys.exit(1)
            # Skip utvec init if trap delegation to u_mode is not supported
            if(mode == privileged_mode_t.USER_MODE and not (rcs.support_umode_trap)):
                continue
            if mode < cfg.init_privileged_mode:
                continue
            tvec_name = trap_vec_reg.name
            tvec_name = tvec_name.lower()
            instr.append("la x{}, {}{}_handler".format(
                cfg.gpr[0], pkg_ins.hart_prefix(hart), tvec_name))
            if(rcs.SATP_MODE != satp_mode_t.BARE and mode != privileged_mode_t.MACHINE_MODE):
                # For supervisor and user mode, use virtual address instead of physical address.
                # Virtual address starts from address 0x0, here only the lower 20 bits are kept
                # as virtual address offset.
                instr.append("slli x{}, x{}, {}\n".format(cfg.gpr[0], cfg.gpr[0], rcs.XLEN - 20) +
                             "srli x{}, x{}, {}".format(cfg.gpr[0], cfg.gpr[0], rcs.XLEN - 20))

            instr.extend(("ori x{}, x{}, {}".format(cfg.gpr[0], cfg.gpr[0], cfg.mtvec_mode),
                          "csrw {}, x{} # {}".format(hex(trap_vec_reg), cfg.gpr[0],
                                                     trap_vec_reg.name)))
        self.gen_section(pkg_ins.get_label("trap_vec_init", hart), instr)

    # ---------------------------------------------------------------------------------------
    # Exception handling routine
    # ---------------------------------------------------------------------------------------

    # Trap handling routine
    def gen_all_trap_handler(self, hart):
        instr = []
        # If PMP isn't supported, generate the relevant trap handler sections as per usual
        if not rcs.support_pmp:
            self.gen_trap_handlers(hart)
            # Ecall handler
            self.gen_ecall_handler(hart)
            # Instruction fault handler
            self.gen_instr_fault_handler(hart)
            # Load fault handler
            self.gen_load_fault_handler(hart)
            # Store fault handler
            self.gen_store_fault_handler(hart)
        # Ebreak handler
        self.gen_ebreak_handler(hart)
        # Illegal instruction handler
        self.gen_illegal_instr_handler(hart)
        # Generate page table fault handling routine
        # Page table fault is always handled in machine mode, as virtual address translation may be
        # broken when page fault happens.
        self.gen_signature_handshake(instr, signature_type_t.CORE_STATUS,
                                     core_status_t.HANDLING_EXCEPTION)
        if not self.page_table_list:
            # TODO
            # self.page_table_list.gen_page_fault_handling_routine(instr)
            pass
        else:
            instr.append("nop")
        self.gen_section(pkg_ins.get_label("pt_fault_handler", hart), instr)

    def gen_trap_handlers(self, hart):
        # TODO
        self.gen_trap_handler_section(hart, "m", privileged_reg_t.MCAUSE,
                                      privileged_reg_t.MTVEC, privileged_reg_t.MTVAL,
                                      privileged_reg_t.MEPC, privileged_reg_t.MSCRATCH,
                                      privileged_reg_t.MSTATUS, privileged_reg_t.MIE,
                                      privileged_reg_t.MIP)

    # Generate the interrupt and trap handler for different privileged mode.
    # The trap handler checks the xCAUSE to determine the type of the exception and jumps to
    # corresponding exeception handling routine.
    def gen_trap_handler_section(self, hart, mode, cause, tvec,
                                 tval, epc, scratch, status, ie, ip):
        # is_interrupt = 1
        tvec_name = ""
        instr = []
        if cfg.mtvec_mode == mtvec_mode_t.VECTORED:
            self.gen_interrupt_vector_table(hart, mode, status, cause, ie, ip, scratch, instr)
        else:
            # Push user mode GPR to kernel stack before executing exception handling,
            # this is to avoid exception handling routine modify user program state
            # unexpectedly
            pkg_ins.push_gpr_to_kernel_stack(
                status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr)
            # Checking xStatus can be optional if ISS (like spike) has different implementation of
            # certain fields compared with the RTL processor.
            if cfg.check_xstatus:
                instr.append("csrr x{}, {} # {}".format(
                    cfg.gpr[0], hex(status), status.name))
            # Use scratch CSR to save a GPR value
            # Check if the exception is caused by an interrupt, if yes, jump to interrupt
            # handler Interrupt is indicated by xCause[XLEN-1]
            instr.append("csrr x{}, {} # {}\n".format(cfg.gpr[0], hex(cause),
                                                      cause.name) +
                         "{}srli x{}, x{}, {}\n".format(pkg_ins.indent, cfg.gpr[0],
                                                        cfg.gpr[0], rcs.XLEN - 1) +
                         "{}bne x{}, x0, {}{}mode_intr_handler".format(pkg_ins.indent,
                                                                       cfg.gpr[0],
                                                                       pkg_ins.hart_prefix(hart),
                                                                       mode))
        # The trap handler will occupy one 4KB page, it will be allocated one entry in
        # the page table with a specific privileged mode.
        if rcs.SATP_MODE != satp_mode_t.BARE:
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align {}".format(cfg.tvec_alignment))
        tvec_name = tvec.name
        self.gen_section(pkg_ins.get_label("{}_handler".format(tvec_name.lower()), hart), instr)

        # Exception handler
        instr = []
        if cfg.mtvec_mode == mtvec_mode_t.VECTORED:
            pkg_ins.push_gpr_to_kernel_stack(
                status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr)
        self.gen_signature_handshake(instr, signature_type_t.CORE_STATUS,
                                     core_status_t.HANDLING_EXCEPTION)
        # TODO
        instr.extend(("csrr x{}, {} # {}".format(cfg.gpr[0], hex(epc), epc.name),
                      "csrr x{}, {} # {}".format(cfg.gpr[0], hex(cause), cause.name),
                      # Check if it's an ECALL exception. Jump to ECALL exception handler
                      # TODO ECALL_SMODE, ECALL_UMODE
                      "li x{}, {} # ECALL_MMODE".format(cfg.gpr[1],
                                                        hex(exception_cause_t.ECALL_MMODE)),
                      "beq x{}, x{}, {}ecall_handler".format(
                      cfg.gpr[0], cfg.gpr[1], pkg_ins.hart_prefix(hart)),
                      # Illegal instruction exception
                      "li x{}, {} # ILLEGAL_INSTRUCTION".format(
                      cfg.gpr[1], hex(exception_cause_t.ILLEGAL_INSTRUCTION)),
                      "beq x{}, x{}, {}illegal_instr_handler".format(
                      cfg.gpr[0], cfg.gpr[1], pkg_ins.hart_prefix(hart)),
                      # Skip checking tval for illegal instruction as it's implementation specific
                      "csrr x{}, {} # {}".format(cfg.gpr[1], hex(tval), tval.name),
                      # use JALR to jump to test_done.
                      "1: la x{}, test_done".format(cfg.scratch_reg),
                      "jalr x1, x{}, 0".format(cfg.scratch_reg)))
        self.gen_section(pkg_ins.get_label("{}mode_exception_handler".format(mode), hart), instr)

    # Generate for interrupt vector table
    def gen_interrupt_vector_table(self, hart, mode, status, cause, ie,
                                   ip, scratch, instr):
        '''In vector mode, the BASE address is shared between interrupt 0 and exception handling.
           When vectored interrupts are enabled, interrupt cause 0, which corresponds to user-mode
           software interrupts, are vectored to the same location as synchronous exceptions. This
           ambiguity does not arise in practice, since user-mode software interrupts are either
           disabled or delegated'''
        instr.extend((".option norvc;", "j {}{}mode_exception_handler".format(
            pkg_ins.hart_prefix(hart), mode)))
        # Redirect the interrupt to the corresponding interrupt handler
        for i in range(1, rcs.max_interrupt_vector_num):
            instr.append("j {}{}mode_intr_vector_{}".format(pkg_ins.hart_prefix(hart), mode, i))
        if not cfg.disable_compressed_instr:
            instr.append(".option rvc;")
        for i in range(1, rcs.max_interrupt_vector_num):
            intr_handler = []
            pkg_ins.push_gpr_to_kernel_stack(
                status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, intr_handler)
            self.gen_signature_handshake(instr=intr_handler,
                                         signature_type=signature_type_t.CORE_STATUS,
                                         core_status=core_status_t.HANDLING_IRQ)
            intr_handler.extend(("csrr x{}, {} # {}".format(
                                 cfg.gpr[0], hex(cause), cause.name),
                                 # Terminate the test if xCause[31] != 0 (indicating exception)
                                 "srli x{}, x{}, {}".format(
                                 cfg.gpr[0], cfg.gpr[0], hex(rcs.XLEN - 1)),
                                 "beqz x{}, 1f".format(cfg.gpr[0])))
            csr_list = [status, cause, ie, ip]
            for csr_t in csr_list:
                self.gen_signature_handshake(
                    instr=intr_handler, signature_type=signature_type_t.WRITE_CSR, csr=csr_t)

            # Jump to commmon interrupt handling routine
            intr_handler.extend(("j {}{}mode_intr_handler".format(pkg_ins.hart_prefix(hart), mode),
                                 "1: la x{}, test_done".format(cfg.scratch_reg),
                                 "jalr x0, x{}, 0".format(cfg.scratch_reg)))
            self.gen_section(pkg_ins.get_label(
                "{}mode_intr_vector_{}".format(mode, i), hart), intr_handler)
    # ECALL trap handler
    # It does some clean up like dump GPRs before communicating with host to terminate the test.
    # User can extend this function if some custom clean up routine is needed.

    def gen_ecall_handler(self, hart):
        instr = []
        self.dump_perf_stats(instr)
        self.gen_register_dump(instr)
        instr.extend(("la x{}, write_tohost".format(cfg.scratch_reg),
                      "jalr x0, x{}, 0".format(cfg.scratch_reg)))
        self.gen_section(pkg_ins.get_label("ecall_handler", hart), instr)

    # Ebreak trap handler
    # When breakpoint exception happens, epc will be written with ebreak instruction
    # itself. Add epc by 4 and resume execution.
    # Note the breakpoint could be triggered by a C.EBREAK instruction, the generated program
    # guarantees that epc + 4 is a valid instruction boundary
    # TODO: Support random operations in debug mode
    # TODO: Support ebreak exception delegation
    # TODO: handshake the correct Xcause CSR based on delegation privil. mode
    def gen_ebreak_handler(self, hart):
        # TODO
        pass

    # Illegal instruction handler
    # Note: Save the illegal instruction to MTVAL is optional in the spec, and mepc could be
    # a virtual address that cannot be used in machine mode handler. As a result, there's no way to
    # know the illegal instruction is compressed or not. This hanlder just simply adds the PC by
    # 4 and resumes execution. The way that the illegal instruction is injected guarantees that
    # PC + 4 is a valid instruction boundary.
    # TODO: handshake the corret Xcause CSR based on delegation setup
    def gen_illegal_instr_handler(self, hart):
        instr = []
        self.gen_signature_handshake(instr, signature_type_t.CORE_STATUS,
                                     core_status_t.ILLEGAL_INSTR_EXCEPTION)
        self.gen_signature_handshake(instr, signature_type_t.WRITE_CSR, privileged_reg_t.MCAUSE)
        instr.extend(("csrr  x{}, {}".format(cfg.gpr[0], hex(privileged_reg_t.MEPC)),
                      "addi  x{}, x{}, 4".format(cfg.gpr[0], cfg.gpr[0]),
                      "csrw  {}, x{}".format(hex(privileged_reg_t.MEPC), cfg.gpr[0])))
        pkg_ins.pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH,
                                          cfg.mstatus_mprv, cfg.sp, cfg.tp, instr)
        instr.append("mret")
        self.gen_section(pkg_ins.get_label("illegal_instr_handler", hart), instr)

    # TODO: handshake correct csr based on delegation
    def gen_instr_fault_handler(self, hart):
        # TODO
        pass

    # TODO: handshake correct csr based on delegation
    def gen_load_fault_handler(self, hart):
        # TODO
        pass

    # TODO: handshake correct csr based on delegation
    def gen_store_fault_handler(self, hart):
        # TODO
        pass

    # ---------------------------------------------------------------------------------------
    # Page table setup
    # ---------------------------------------------------------------------------------------

    # Create page table if virtual address translation is supported.
    # The page is created based on the address translation mode - SV32, SV39, SV48
    # Right now only the lowest level 4KB page table is configured as leaf page table entry (PTE),
    # all the other super pages are link PTE.
    def create_page_table(self, hart):
        # TODO
        pass

    # Generate the page table section of the program
    # The page table is generated as a group of continuous 4KB data sections.
    def gen_page_table_section(self, hart):
        # TODO
        pass

    # Only extend this function if the core utilizes a PLIC for handling interrupts
    # In this case, the core will write to a specific location as the response to the interrupt, and
    # external PLIC unit can detect this response and process the interrupt clean up accordingly.
    def gen_plic_section(self, interrupt_handler_instr):
        # TODO
        pass

    # Interrupt handler routine
    def gen_interrupt_handler_section(self, mode, hart):
        interrupt_handler_instr = []
        # ls_unit = "w" if rcs.XLEN == 32 else "d"
        if mode < cfg.init_privileged_mode:
            return
        if(mode is privileged_mode_t.USER_MODE and not (rcs.support_umode_trap)):
            return
        if mode == privileged_mode_t.MACHINE_MODE:
            mode_prefix = "m"
            status = privileged_reg_t.MSTATUS
            ip = privileged_reg_t.MIP
            ie = privileged_reg_t.MIE
            scratch = privileged_reg_t.MSCRATCH
        elif mode is privileged_mode_t.SUPERVISOR_MODE:
            mode_prefix = "s"
            status = privileged_reg_t.SSTATUS
            ip = privileged_reg_t.SIP
            ie = privileged_reg_t.SIE
            scratch = privileged_reg_t.SSCRATCH
        elif mode == privileged_mode_t.USER_MODE:
            mode_prefix = "u"
            status = privileged_reg_t.USTATUS
            ip = privileged_reg_t.UIP
            ie = privileged_reg_t.UIE
            scratch = privileged_reg_t.USCRATCH
        else:
            logging.critical("Unsupported mode: {}".format(mode.name))
            sys.exit(1)
        # If nested interrupts are enabled, set xSTATUS.xIE in the interrupt handler
        # to re-enable interrupt handling capabilities
        if cfg.enable_nested_interrupt:
            interrupt_handler_instr.extend(("csrr x{}, {}".format(cfg.gpr[0], hex(scratch)),
                                            "bgtz x{}, 1f".format(cfg.gpr[0]),
                                            "csrwi {}, 0x1".format(hex(scratch))))

            if status == privileged_reg_t.MSTATUS:
                interrupt_handler_instr.append("csrsi {}, {}".format(hex(status), hex(8)))
            elif status == privileged_reg_t.SSTATUS:
                interrupt_handler_instr.append("csrsi {}, {}".format(hex(status), hex(2)))
            elif status == privileged_reg_t.USTATUS:
                interrupt_handler_instr.append("csrsi {}, {}".format(hex(status), hex(1)))
            else:
                logging.critical("Unsupported status {}".format(status.name))
                sys.exit(1)

            interrupt_handler_instr.append("1: csrwi {},0".format(hex(scratch)))
        # Read back interrupt related privileged CSR
        # The value of these CSR are checked by comparing with spike simulation result.
        to_extend_interrupt_hanlder_instr = ["csrr  x{}, {} # {};".format(cfg.gpr[0],
                                                                          hex(status),
                                                                          status.name),
                                             "csrr  x{}, {} # {};".format(cfg.gpr[0],
                                                                          hex(ie), ie.name),
                                             "csrr  x{}, {} # {};".format(cfg.gpr[0],
                                                                          hex(ip), ip.name),
                                             "csrrc x{}, {}, x{} # {};".format(cfg.gpr[0],
                                                                               hex(ip),
                                                                               cfg.gpr[0],
                                                                               ip.name)]
        interrupt_handler_instr.extend(to_extend_interrupt_hanlder_instr)
        self.gen_plic_section(interrupt_handler_instr)
        # Restore user mode GPR value from kernel stack before return
        pkg_ins.pop_gpr_from_kernel_stack(status, scratch, cfg.mstatus_mprv,
                                          cfg.sp, cfg.tp, interrupt_handler_instr)
        interrupt_handler_instr.append("{}ret;".format(mode_prefix))

        if rcs.SATP_MODE != satp_mode_t.BARE:
            # The interrupt handler will use one 4KB page
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")

        self.gen_section(pkg_ins.get_label("{}mode_intr_handler".format(mode_prefix), hart),
                         interrupt_handler_instr)

    # ---------------------------------------------------------------------------------------
    # Helper functions
    # ---------------------------------------------------------------------------------------

    # Format a code section, without generating it
    def format_section(self, instr):
        # TODO
        pass

    # Generate a code section
    def gen_section(self, label, instr):
        if label != "":
            string = pkg_ins.format_string("{}:".format(label), pkg_ins.LABEL_STR_LEN)
            self.instr_stream.append(string)
        for items in instr:
            string = pkg_ins.indent + items
            self.instr_stream.append(string)
        self.instr_stream.append("")

    # Dump performance CSRs if applicable
    def dump_perf_stats(self, instr):
        # TODO
        pass

    # Write the generated program to a file
    def gen_test_file(self, test_name):
        file = open(test_name, "w+")
        for items in self.instr_stream:
            file.write("{}\n".format(items))

        file.close()
        logging.info("{} is generated".format(test_name))

    # Helper function to generate the proper sequence of handshake instructions
    # to signal the testbench (see riscv_signature_pkg.sv)
    def gen_signature_handshake(self, instr, signature_type,
                                core_status=core_status_t.INITIALIZED,
                                test_result=test_result_t.TEST_FAIL,
                                csr=privileged_reg_t.MSCRATCH,
                                addr_label = ""):
        if cfg.require_signature_addr:
            instr.extend(("li x{}, {}".format(cfg.gpr[1], hex(cfg.signature_addr))))
            # A single data word is written to the signature address.
            # Bits [7:0] contain the signature_type of CORE_STATUS, and the upper
            # XLEN-8 bits contain the core_status_t data.
            if signature_type == signature_type_t.CORE_STATUS:
                instr.extend(("li x{}, {}".format(cfg.gpr[0], hex(core_status)),
                              "slli x{}, x{}, 8".format(cfg.gpr[0], cfg.gpr[0]),
                              "addi x{}, x{}, {}".format(cfg.gpr[0], cfg.gpr[0],
                                                         hex(signature_type)),
                              "sw x{}, 0(x{})".format(cfg.gpr[0], cfg.gpr[1])))
            # A single data word is written to the signature address.
            # Bits [7:0] contain the signature_type of TEST_RESULT, and the upper
            # XLEN-8 bits contain the test_result_t data.
            elif signature_type == test_result_t.TEST_RESULT:
                instr.extend(("li x{}, {}".format(cfg.gpr[0], hex(test_result)),
                              "slli x{}, x{}, 8".format(cfg.gpr[0], cfg.gpr[0]),
                              "addi x{}, x{}, {}".format(cfg.gpr[0], cfg.gpr[0],
                                                         hex(signature_type)),
                              "sw x{}, 0(x{})".format(cfg.gpr[0], cfg.gpr[1])))
            # The first write to the signature address contains just the
            # signature_type of WRITE_GPR.
            # It is followed by 32 consecutive writes to the signature address,
            # each writing the data contained in one GPR, starting from x0 as the
            # first write, and ending with x31 as the 32nd write.
            elif signature_type == signature_type_t.WRITE_GPR:
                instr.extend(("li x{}, {}".format(cfg.gpr[0], hex(signature_type)),
                              "sw x{}, 0(x{})".format(cfg.gpr[0], cfg.gpr[1])))
                for i in range(32):
                    instr.append("sw x{},0(x{})".format(i, cfg.gpr[1]))
            # The first write to the signature address contains the
            # signature_type of WRITE_CSR in bits [7:0], and the CSR address in
            # the upper XLEN-8 bits.
            # It is followed by a second write to the signature address,
            # containing the data stored in the specified CSR.
            elif signature_type == signature_type_t.WRITE_CSR:
                if csr not in rcs.implemented_csr:
                    return
                instr.extend(("li x{}, {}".format(cfg.gpr[0], hex(csr)),
                              "slli x{}, x{}, 8".format(cfg.gpr[0], cfg.gpr[0]),
                              "addi x{}, x{}, {}".format(cfg.gpr[0], cfg.gpr[0],
                                                         hex(signature_type)),
                              "sw x{}, 0(x{})".format(cfg.gpr[0], cfg.gpr[1]),
                              "csrr x{}, {}".format(cfg.gpr[0], hex(csr)),
                              "sw x{}, 0(x{})".format(cfg.gpr[0], cfg.gpr[1])))
            else:
                logging.critical("signature_type is not defined")
                sys.exit(1)

    # ---------------------------------------------------------------------------------------
    # Inject directed instruction stream
    # ---------------------------------------------------------------------------------------

    def add_directed_instr_stream(self, name, ratio):
        self.directed_instr_stream_ratio[name] = ratio
        logging.info("Adding directed instruction stream:%0s ratio:%0d/1000", name, ratio)

    def get_directed_instr_stream(self):
        opts = []
        for i in range(cfg.max_directed_instr_stream_seq):
            arg = "directed_instr_{}".format(i)
            stream_name_opts = "stream_name_{}".format(i)
            stream_freq_opts = "stream_freq_{}".format(i)
            if cfg.args_dict[arg]:
                val = cfg.args_dict[arg]
                opts = val.split(",")
                if len(opts) != 2:
                    logging.critical(
                        "Incorrect directed instruction format : %0s, expect: name,ratio", val)
                    sys.exit(1)
                else:
                    self.add_directed_instr_stream(opts[0], int(opts[1]))
            elif cfg.args_dict[stream_name_opts] and cfg.args_dict[stream_freq_opts]:
                stream_name = cfg.args_dict[stream_name_opts]
                stream_freq = cfg.args_dict[stream_freq_opts]
                self.add_directed_instr_stream(stream_name, stream_freq)

    # Generate directed instruction stream based on the ratio setting
    def generate_directed_instr_stream(self, hart = 0, label = "", original_instr_cnt = 0,
                                       min_insert_cnt = 0, kernel_mode = 0, instr_stream = []):
        instr_insert_cnt = 0
        idx = 0
        if cfg.no_directed_instr:
            return
        for instr_stream_name in self.directed_instr_stream_ratio:
            instr_insert_cnt = int(original_instr_cnt *
                                   self.directed_instr_stream_ratio[instr_stream_name] // 1000)
            if instr_insert_cnt <= min_insert_cnt:
                instr_insert_cnt = min_insert_cnt
            logging.info("Insert directed instr stream %0s %0d/%0d times",
                         instr_stream_name, instr_insert_cnt, original_instr_cnt)
            for i in range(instr_insert_cnt):
                name = "{}_{}".format(instr_stream_name, i)
                object_h = factory(instr_stream_name)
                object_h.name = name
                if not object_h:
                    logging.critical("Cannot create instr stream %0s", name)
                    sys.exit(1)
                new_instr_stream = copy.deepcopy(object_h)
                if new_instr_stream:
                    new_instr_stream.hart = hart
                    new_instr_stream.label = "{}_{}".format(label, idx)
                    new_instr_stream.kernel_mode = kernel_mode
                    new_instr_stream.randomize()
                    instr_stream.append(new_instr_stream)
                else:
                    logging.critical("Cannot Create instr stream %0s", name)
                    sys.exit(1)
                idx += 1
        random.shuffle(instr_stream)

    # ----------------------------------------------------------------------------------
    # Generate the debug ROM, and any related programs
    # ----------------------------------------------------------------------------------

    def gen_debug_rom(self, hart):
        # TODO
        pass

    # ----------------------------------------------------------------------------------
    # Vector extension generation
    # ----------------------------------------------------------------------------------

    def randomize_vec_gpr_and_csr(self):
        # TODO
        pass
