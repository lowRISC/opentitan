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

import subprocess
import logging
import random
import copy
import sys
from bitstring import BitArray
from pygen_src.riscv_instr_sequence import riscv_instr_sequence
from pygen_src.riscv_instr_pkg import pkg_ins, privileged_reg_t, privileged_mode_t, mtvec_mode_t
from pygen_src.riscv_instr_gen_config import cfg, args, args_dict
from pygen_src.target.rv32i import riscv_core_setting as rcs
from pygen_src.riscv_instr_stream import riscv_rand_instr_stream
from pygen_src.riscv_utils import factory
'''
    RISC-V assembly program generator

    This is the main class to generate a complete RISC-V program, including the init routine,
    instruction section, data section, stack section, page table, interrupt and exception
    handling etc. Check gen_program() function to see how the program is generated.
'''


class riscv_asm_program_gen:

    def __init__(self):
        self.instr_stream = []
        self.directed_instr_stream_ratio = {}
        self.hart = 0
        self.page_table_list = []
        self.main_program = []
        self.sub_program = []

    # Main function to generate the whole program

    # This is the main function to generate all sections of the program.
    def gen_program(self):
        # Generate program header
        self.instr_stream.clear()
        self.gen_program_header()
        for hart in range(cfg.num_of_harts):
            # Commenting out for now
            # sub_program_name = []
            self.instr_stream.append(f"h{int(hart)}_start:")
            if(not(cfg.bare_program_mode)):
                self.setup_misa()
                # Create all page tables
                self.create_page_table(hart)
                # Setup privileged mode registers and enter target privileged mode
                self.pre_enter_privileged_mode(hart)
            # Init section
            self.gen_init_section(hart)
            # To DO
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
                self.gen_test_done()

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
                                                original_instr_cnt=self.main_program[hart].instr_cnt,
                                                min_insert_cnt=1,
                                                instr_stream=self.main_program[hart].directed_instr)
            self.main_program[hart].gen_instr(is_main_program=1, no_branch=cfg.no_branch_jump)

            self.main_program[hart].post_process_instr()
            self.main_program[hart].generate_instr_stream()
            logging.info("Generating main program instruction stream...done")
            self.instr_stream.extend(self.main_program[hart].instr_string_list)
            """
            If PMP is supported, need to jump from end of main program
            to test_done section at the end of main_program, as the test_done
            will have moved to the beginning of the program
            """
            self.instr_stream.append("{}j test_done".format(pkg_ins.indent))
            '''
            Test done section
            If PMP isn't supported, generate this in the normal location
            '''
            if(hart == 0 and not(rcs.support_pmp)):
                self.gen_test_done()

            logging.info("Main/sub program generation...done")
            # program end
            self.gen_program_end(hart)
            for hart in range(cfg.num_of_harts):
                self.gen_data_page_begin(hart)
                if(cfg.no_data_page):
                    self.gen_data_page()

                    if((hart == 0) and ("RV32A" in rcs.supported_isa)):
                        self.gen_data_page(hart, amo = 1)

            self.gen_stack_section(hart)
            if(not cfg.bare_program_mode):
                self.gen_kernel_sections(hart)

    def gen_kernel_sections(self, hart):
        if(rcs.SATP_MODE != "BARE"):
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")
        self.instr_stream.append(pkg_ins.get_label("kernel_instr_start:", hart))
        self.instr_stream.append(".text")

        self.gen_all_trap_handler(hart)
        for mode in rcs.supported_privileged_mode:
            self.gen_interrupt_handler_section(mode, hart)

        self.gen_kernel_stack_section(hart)

    def gen_kernel_program(self, hart, seq):
        pass

    def gen_sub_program(self, hart, sub_program,
                        sub_program_name, num_sub_program,
                        is_debug = 0, prefix = "sub"):
        pass

    def gen_callstack(self, main_program, sub_program,
                      sub_program_name, num_sub_program):
        pass

    def insert_sub_program(self, sub_program, instr_list):
        pass

    def gen_program_header(self):
        string = []
        self.instr_stream.append(".include \"user_define.h\"")
        self.instr_stream.append(".globl _start")
        self.instr_stream.append(".section .text")
        if(cfg.disable_compressed_instr):
            self.instr_stream.append(".option norvc;")
        string.append(".include \"user_init.s\"")
        string.append("csrr x5, mhartid")

        for hart in range(cfg.num_of_harts):
            string.append("li x6, {}\n{}beq x5, x6, {}f".format(hart, pkg_ins.indent, hart))

        self.gen_section("_start", string)

        for hart in range(cfg.num_of_harts):
            self.instr_stream.append("{}: j h{}_start".format(hart, hart))

    def gen_program_end(self, hart):
        if(hart == 0):
            self.gen_section("write_tohost", ["sw gp, tohost, t5"])
            self.gen_section("_exit", ["j write_tohost"])

    def gen_data_page_begin(self, hart):
        self.instr_stream.append(".section .data")
        if (hart == 0):
            self.instr_stream.append(".align 6; .global tohost; tohost: .dword 0;")
            self.instr_stream.append(".align 6; .global fromhost; fromhost: .dword 0;")

    def gen_data_page(self, hart, is_kernel = 0, amo = 0):
        pass

    def gen_stack_section(self, hart):
        hart_prefix_string = pkg_ins.hart_prefix(hart)
        if(cfg.use_push_data_section):
            self.instr_stream.append(
                ".pushsection .{}user_stack,\"aw\",@progbits;".format(hart_prefix_string))
        else:
            self.instr_stream.append(
                ".section .{}user_stack,\"aw\",@progbits;".format(hart_prefix_string))
        if(rcs.SATP_MODE != "BARE"):
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")

        self.instr_stream.append(pkg_ins.get_label("user_stack_start:", hart))
        self.instr_stream.append(".rept {}".format(cfg.kernel_stack_len - 1))
        self.instr_stream.append(".{}byte 0x0".format(rcs.XLEN // 8))
        self.instr_stream.append(".endr")
        self.instr_stream.append(pkg_ins.get_label("user_stack_end:", hart))
        self.instr_stream.append(".{}byte 0x0".format(rcs.XLEN // 8))
        if (cfg.use_push_data_section):
            self.instr_stream.push_back(".popsection;")

    def gen_kernel_stack_section(self, hart):
        hart_prefix_string = pkg_ins.hart_prefix(hart)
        if(cfg.use_push_data_section):
            self.instr_stream.append(
                ".pushsection .{}kernel_stack,\"aw\",@progbits;".format(hart_prefix_string))
        else:
            self.instr_stream.append(
                ".section .{}kernel_stack,\"aw\",@progbits;".format(hart_prefix_string))
        if(rcs.SATP_MODE != "BARE"):
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")

        self.instr_stream.append(pkg_ins.get_label("kernel_stack_start:", hart))
        self.instr_stream.append(".rept {}".format(cfg.kernel_stack_len - 1))
        self.instr_stream.append(".{}byte 0x0".format(rcs.XLEN // 8))
        self.instr_stream.append(".endr")
        self.instr_stream.append(pkg_ins.get_label("kernel_stack_end:", hart))
        self.instr_stream.append(".{}byte 0x0".format(rcs.XLEN // 8))
        if (cfg.use_push_data_section):
            self.instr_stream.push_back(".popsection;")

    def gen_init_section(self, hart):
        string = pkg_ins.format_string("init:", pkg_ins.LABEL_STR_LEN)
        self.instr_stream.append(string)
        self.init_gpr()
        # Init stack pointer to point to the end of the user stack
        string = "{}la x{}, {}user_stack_end".format(
            pkg_ins.indent, cfg.sp.value, pkg_ins.hart_prefix(hart))
        self.instr_stream.append(string)
        if (cfg.enable_floating_point):
            self.init_floating_point_gpr()
        if (cfg.enable_vector_extension):
            self.init_vector_engine()
        self.core_is_initialized()
        self.gen_dummy_csr_write()

        if (rcs.support_pmp):
            string = pkg_ins.indent + "j main"
            self.instr_stream.append(string)

    def setup_misa(self):
        # TO DO
        misa = 0b01000000
        self.instr_stream.append("{}li x{}, {}".format(pkg_ins.indent, cfg.gpr[0].value, hex(misa)))
        self.instr_stream.append("{}csrw misa, x{}".format(pkg_ins.indent, cfg.gpr[0].value))

    def core_is_initialized(self):
        pass

    def gen_dummy_csr_write(self):
        pass

    def init_gpr(self):
        reg_val = BitArray(uint = 0, length = pkg_ins.DATA_WIDTH)
        dist_lst = []

        for dist_val in range(5):
            if dist_val == 0:
                reg_val = BitArray(hex='0x0')
            elif dist_val == 1:
                reg_val = BitArray(hex='0x80000000')
            elif dist_val == 2:
                temp = random.randrange(0x1, 0xf)
                reg_val = BitArray(hex(temp), length=32)
            elif dist_val == 3:
                temp = random.randrange(0x10, 0xefffffff)
                reg_val = BitArray(hex(temp), length=32)
            else:
                temp = random.randrange(0xf0000000, 0xffffffff)
                reg_val = BitArray(hex(temp), length=32)
            dist_lst.append(reg_val)

        for i in range(32):
            init_string = "{}li x{}, {}".format(pkg_ins.indent, i, random.choice(dist_lst))
            self.instr_stream.append(init_string)

    def init_floating_point_gpr(self):
        pass

    def init_vector_engine(self):
        pass

    def gen_test_done(self):
        string = pkg_ins.format_string("test_done:", pkg_ins.LABEL_STR_LEN)
        self.instr_stream.append(string)
        self.instr_stream.append(pkg_ins.indent + "li gp, 1")

        if(cfg.bare_program_mode):
            self.instr_stream.append(pkg_ins.indent + "j write_tohost")
        else:
            self.instr_stream.append(pkg_ins.indent + "ecall")

    def gen_register_dump(self):
        string = ""
        # load base address
        string = "{}la x{}, _start".format(pkg_ins.indent, cfg.gpr[0].value)
        self.instr_stream.append(string)

        # Generate sw/sd instructions
        for i in range(32):
            if (rcs.XLEN == 64):
                string = "{}sd x{}, {}(x{})".format(
                    pkg_ins.indent, i, i * (rcs.XLEN / 8), cfg.gpr[0].value)
            else:
                string = "{}sw x{}, {}(x{})".format(
                    pkg_ins.indent, i, int(i * (rcs.XLEN / 8)), cfg.gpr[0].value)
            self.instr_stream.append(string)

    def pre_enter_privileged_mode(self, hart):
        instr = []
        string = []

        string.append("la x{}, {}kernel_stack_end".format(cfg.tp.value, pkg_ins.hart_prefix(hart)))
        self.gen_section(pkg_ins.get_label("kernel_sp", hart), string)

        if(not cfg.no_delegation and (cfg.init_privileged_mode != "MACHINE_MODE")):
            self.gen_delegation(hart)
        self.trap_vector_init(hart)
        self.setup_pmp(hart)

        if(cfg.virtual_addr_translation_on):
            self.page_table_list.process_page_table(instr)
            self.gen_section(pkg_ins.get_label("process_pt", hart), instr)
        # Commenting for now
        # self.setup_epc(hart)

        if(rcs.support_pmp):
            self.gen_privileged_mode_switch_routine(hart)

    def gen_privileged_mode_switch_routine(self, hart):
        pass

    def setup_epc(self, hart):
        instr = []
        instr.append("la x{}, {}init".format(cfg.gpr[0].value, pkg_ins.hart_prefix(hart)))
        # if(cfg.virtual_addr_translation_on):
        # instr.append("slli x{}, x{}")
        # TODO
        mode_name = cfg.init_privileged_mode
        instr.append("csrw mepc, x{}".format(cfg.gpr[0].value))
        if(not rcs.support_pmp):  # TODO
            instr.append("j {}init_{}".format(pkg_ins.hart_prefix(hart), mode_name.name.lower()))

        self.gen_section(pkg_ins.get_label("mepc_setup", hart), instr)

    def setup_pmp(self, hart):
        pass

    def gen_delegation(self, hart):
        self.gen_delegation_instr(hart, "MEDELEG", "MIDELEG",
                                  cfg.m_mode_exception_delegation,
                                  cfg.m_mode_interrupt_delegation)
        if(rcs.support_umode_trap):
            self.gen_delegation_instr(hart, "SEDELEG", "SIDELEG",
                                      cfg.s_mode_exception_delegation,
                                      cfg.s_mode_interrupt_delegation)

    def gen_delegation_instr(self, hart, edeleg, ideleg,
                             edeleg_enable, ideleg_enable):
        pass

    def trap_vector_init(self, hart):
        instr = []
        for items in rcs.supported_privileged_mode:
            if(items == "MACHINE_MODE"):
                trap_vec_reg = privileged_reg_t.MTVEC
            elif(items == "SUPERVISOR_MODE"):
                trap_vec_reg = privileged_reg_t.STVEC
            elif(items == "USER_MODE"):
                trap_vec_reg = privileged_reg_t.UTVEC
            else:
                logging.critical(
                    "[riscv_asm_program_gen] Unsupported privileged_mode {}".format(items))

            if(items == "USER_MODE" and not (rcs.support_umode_trap)):
                continue

            if(items < cfg.init_privileged_mode.name):
                continue

            tvec_name = trap_vec_reg.name
            tvec_name = tvec_name.lower()
            instr.append("la x{}, {}{}_handler".format(
                cfg.gpr[0].value, pkg_ins.hart_prefix(hart), tvec_name))
            if(rcs.SATP_MODE != "BARE" and items != "MACHINE_MODE"):
                instr.append("slli x{}, x{}, {}\n".format(cfg.gpr[0].value,
                                                          cfg.gpr[0].value, rcs.XLEN - 20) +
                             "srli x{}, x{}, {}".format(cfg.gpr[0].value,
                                                        cfg.gpr[0].value, rcs.XLEN - 20))

            instr.append("ori x{}, x{}, {}".format(
                cfg.gpr[0].value, cfg.gpr[0].value, cfg.mtvec_mode.value))
            instr.append("csrw {}, x{} # {}".format(
                hex(trap_vec_reg.value), cfg.gpr[0].value, trap_vec_reg.name))

        self.gen_section(pkg_ins.get_label("trap_vec_init", hart), instr)

    def gen_all_trap_handler(self, hart):
        if(not rcs.support_pmp):
            self.gen_trap_handlers(hart)
            self.gen_ecall_handler(hart)
            self.gen_instr_fault_handler(hart)
            self.gen_load_fault_handler(hart)
            self.gen_store_fault_handler(hart)

    def gen_trap_handlers(self, hart):
        self.gen_trap_handler_section(hart, "m", privileged_reg_t.MCAUSE,
                                      privileged_reg_t.MTVEC, privileged_reg_t.MTVAL,
                                      privileged_reg_t.MEPC, privileged_reg_t.MSCRATCH,
                                      privileged_reg_t.MSTATUS, privileged_reg_t.MIE,
                                      privileged_reg_t.MIP)

    def gen_trap_handler_section(self, hart, mode, cause, tvec,
                                 tval, epc, scratch, status, ie, ip):
        is_interrupt = 1
        tvec_name = ""
        instr = []
        if (cfg.mtvec_mode == mtvec_mode_t.VECTORED):
            self.gen_interrupt_vector_table(hart, mode, status, cause, ie, ip, scratch, instr)
        else:
            # Push user mode GPR to kernel stack before executing exception handling,
            # this is to avoid exception handling routine modify user program state
            # unexpectedly
            # TODO
            pkg_ins.push_gpr_to_kernel_stack(
                status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr)
        # The trap handler will occupy one 4KB page, it will be allocated one entry in
        # the page table with a specific privileged mode.

        if (rcs.SATP_MODE != "BARE"):
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align {}".format(cfg.tvec_alignment))

        tvec_name = tvec.name
        self.gen_section(pkg_ins.get_label("{}_handler".format(tvec_name.lower()), hart), instr)

        # TODO Exception handler

    def gen_interrupt_vector_table(self, hart, mode, status, cause, ie,
                                   ip, scratch, instr):
        pass

    def gen_ecall_handler(self, hart):
        string = ""
        string = pkg_ins.format_string(pkg_ins.get_label(
            "ecall_handler:", hart), pkg_ins.LABEL_STR_LEN)
        self.instr_stream.append(string)
        self.dump_perf_stats()
        self.gen_register_dump()
        string = pkg_ins.format_string(" ", pkg_ins.LABEL_STR_LEN)
        string = string + "j write_tohost"
        self.instr_stream.append(string)

    def gen_ebreak_handler(self, hart):
        pass

    def gen_illegal_instr_handler(self, hart):
        pass

    def gen_instr_fault_handler(self, hart):
        pass

    def gen_load_fault_handler(self, hart):
        pass

    def gen_store_fault_handler(self, hart):
        pass

    def create_page_table(self, hart):
        pass

    def gen_page_table_section(self, hart):
        pass

    def gen_plic_section(self, interrupt_handler_instr):
        pass

    def gen_interrupt_handler_section(self, mode, hart):
        interrupt_handler_instr = []
        ls_unit = "w" if (rcs.XLEN == 32) else "d"
        # TODO
        # if(mode.value < cfg.init_privileged_mode):
        # return
        if(mode is privileged_mode_t.USER_MODE.name and not (rcs.support_umode_trap)):
            return
        if(mode == privileged_mode_t.MACHINE_MODE.name):
            mode_prefix = "m"
            status = privileged_reg_t.MSTATUS
            ip = privileged_reg_t.MIP
            ie = privileged_reg_t.MIE
            scratch = privileged_reg_t.MSCRATCH
        elif(mode is privileged_mode_t.SUPERVISOR_MODE.name):
            mode_prefix = "s"
            status = privileged_reg_t.SSTATUS
            ip = privileged_reg_t.SIP
            ie = privileged_reg_t.SIE
            scratch = privileged_reg_t.SSCRATCH
        elif(mode == privileged_mode_t.USER_MODE.name):
            mode_prefix = "u"
            status = privileged_reg_t.USTATUS
            ip = privileged_reg_t.UIP
            ie = privileged_reg_t.UIE
            scratch = privileged_reg_t.USCRATCH
        else:
            logging.critical("Unsupported mode: %0s" % (mode))

        if(cfg.enable_nested_interrupt):
            interrupt_handler_instr.append("csrr x%0d, 0x%0x" % (cfg.gpr[0].value, scratch.value))
            interrupt_handler_instr.append("bgtz x%0d, 1f" % (cfg.gpr[0].value))
            interrupt_handler_instr.append("csrwi 0x%0x, 0x1" % (scratch.value))

            if(status == privileged_reg_t.MSTATUS):
                interrupt_handler_instr.append("csrsi 0x%0x, 0x%0x" % (status.value, 8))
            elif(status == privileged_reg_t.SSTATUS):
                interrupt_handler_instr.append("csrsi 0x%0x, 0x%0x" % (status.value, 2))
            elif(status == privileged_reg_t.USTATUS):
                interrupt_handler_instr.append("csrsi 0x%0x, 0x%0x" % (status.value, 1))
            else:
                logging.critical("Unsupported status %0s" % (status.value))

            interrupt_handler_instr.append("1: csrwi 0x%0x,0" % (scratch.value))

        to_extend_interrupt_hanlder_instr = ["csrr  x%0d, 0x%0x # %0s;" % (cfg.gpr[0].value,
                                                                           status.value,
                                                                           status.name),
                                             "csrr  x%0d, 0x%0x # %0s;" % (cfg.gpr[0].value,
                                                                           ie.value, ie.name),
                                             "csrr  x%0d, 0x%0x # %0s;" % (cfg.gpr[0].value,
                                                                           ip.value, ip.name),
                                             "csrrc x%0d, 0x%0x, x%0d # %0s;" % (cfg.gpr[0].value,
                                                                                 ip.value,
                                                                                 cfg.gpr[0].value,
                                                                                 ip.name)]
        interrupt_handler_instr.extend(to_extend_interrupt_hanlder_instr)
        self.gen_plic_section(interrupt_handler_instr)
        pkg_ins.pop_gpr_from_kernel_stack(status.name, scratch.name, cfg.mstatus_mprv,
                                          cfg.sp, cfg.tp, interrupt_handler_instr)
        interrupt_handler_instr.append("%0sret;" % (mode_prefix))

        if(rcs.SATP_MODE != "BARE"):
            self.instr_stream.append(".align 12")
        else:
            self.instr_stream.append(".align 2")

        self.gen_section(pkg_ins.get_label("%0smode_intr_handler" %
                                           (mode_prefix), hart), interrupt_handler_instr)

    def format_section(self, instr):
        pass

    def gen_section(self, label, instr):
        if(label != ""):
            string = pkg_ins.format_string("{}:".format(label), pkg_ins.LABEL_STR_LEN)
            self.instr_stream.append(string)
        for items in instr:
            string = pkg_ins.indent + items
            self.instr_stream.append(string)
        self.instr_stream.append("")

    def dump_perf_stats(self):
        pass

    def gen_test_file(self, test_name):
        subprocess.run(["mkdir", "-p", "out/asm_tests"])
        file = open("./out/asm_tests/{}".format(test_name), "w+")
        for items in self.instr_stream:
            file.write("{}\n".format(items))

        file.close()
        logging.info("%0s is generated", test_name)

    def gen_signature_handshake(self, instr, signature_type, core_status = "INITIALIZED",
                                test_result = "TEST_FAIL", csr = "MSCRATCH", addr_label = ""):
        pass

    def add_directed_instr_stream(self, name, ratio):
        self.directed_instr_stream_ratio[name] = ratio
        logging.info("Adding directed instruction stream:%0s ratio:%0d/1000", name, ratio)

    def get_directed_instr_stream(self):
        opts = []
        for i in range(cfg.max_directed_instr_stream_seq):
            arg = "directed_instr_{}".format(i)
            stream_name_opts = "stream_name_{}".format(i)
            stream_freq_opts = "stream_freq_{}".format(i)
            if(arg in args):
                val = args_dict[arg]
                opts = val.split(",")
                if(len(opts) != 2):
                    logging.critical(
                        "Incorrect directed instruction format : %0s, expect: name,ratio", val)
                else:
                    self.add_directed_instr_stream(opts[0], int(opts[1]))
            elif(stream_name_opts in args and stream_freq_opts in args):
                stream_name = args_dict[stream_name_opts]
                stream_freq = args_dict[stream_freq_opts]
                self.add_directed_instr_stream(stream_name, stream_freq)

    def generate_directed_instr_stream(self, hart = 0, label = "", original_instr_cnt = 0,
                                       min_insert_cnt = 0, kernel_mode = 0, instr_stream = []):
        instr_insert_cnt = 0
        idx = 0
        if(cfg.no_directed_instr):
            return
        for instr_stream_name in self.directed_instr_stream_ratio:
            instr_insert_cnt = int(original_instr_cnt *
                                   self.directed_instr_stream_ratio[instr_stream_name] // 1000)
            if(instr_insert_cnt <= min_insert_cnt):
                instr_insert_cnt = min_insert_cnt
            logging.info("Insert directed instr stream %0s %0d/%0d times",
                         instr_stream_name, instr_insert_cnt, original_instr_cnt)
            for i in range(instr_insert_cnt):
                name = "{}_{}".format(instr_stream_name, i)
                object_h = factory(instr_stream_name)
                object_h.name = name
                if(object_h is None):
                    logging.critical("Cannot create instr stream %0s", name)
                    sys.exit(1)
                new_instr_stream = copy.copy(object_h)
                if(new_instr_stream):
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

    def gen_debug_rom(self, hart):
        pass
