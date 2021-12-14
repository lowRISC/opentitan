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
import vsc
from importlib import import_module
from pygen_src.riscv_instr_pkg import (pkg_ins, privileged_reg_t,
                                       privileged_mode_t, satp_mode_t)
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_privil_reg import riscv_privil_reg
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


# This class provides some common routines for privileged mode operations
@vsc.randobj
class riscv_privileged_common_seq():
    def __init___(self):
        self.hart = 0
        self.mstatus = vsc.attr(riscv_privil_reg)
        self.mie = vsc.attr(riscv_privil_reg)
        self.sstatus = vsc.attr(riscv_privil_reg)
        self.sie = vsc.attr(riscv_privil_reg)
        self.ustatus = vsc.attr(riscv_privil_reg)
        self.uie = vsc.attr(riscv_privil_reg)

    def enter_privileged_mode(self, mode, instrs):
        label = pkg_ins.format_string("{}init_{}:"
                                      .format(pkg_ins.hart_prefix(self.hart), mode.name),
                                      pkg_ins.LABEL_STR_LEN)
        ret_instr = ["mret"]
        regs = vsc.list_t(vsc.attr(riscv_privil_reg()))
        label = label.lower()
        self.setup_mmode_reg(mode, regs)
        if mode == privileged_mode_t.SUPERVISOR_MODE:
            self.setup_smode_reg(mode, regs)
        if mode == privileged_mode_t.USER_MODE:
            self.setup_umode_reg(mode, regs)
        if cfg.virtual_addr_translation_on:
            self.setup_satp(instrs)
        self.gen_csr_instr(regs, instrs)
        # Use mret/sret to switch to the target privileged mode
        instrs.append(ret_instr[0])
        for i in range(len(instrs)):
            instrs[i] = pkg_ins.indent + instrs[i]
        instrs.insert(0, label)

    def setup_mmode_reg(self, mode, regs):
        self.mstatus = riscv_privil_reg()
        self.mstatus.init_reg(privileged_reg_t.MSTATUS)
        self.mstatus_set_field(mode, regs)
        self.mie_set_field(mode, regs)

    def setup_smode_reg(self, mode, regs):
        self.sstatus = riscv_privil_reg()
        self.sstatus.init_reg(privileged_reg_t.SSTATUS)
        self.sstatus.randomize()
        self.sstatus_set_field(mode, regs)
        self.sie_set_field(mode, regs)

    def setup_umode_reg(self, mode, regs):
        # For implementations that do not provide any U-mode CSRs, return immediately
        if not rcs.support_umode_trap:
            return
        self.ustatus = riscv_privil_reg()
        self.ustatus.init_reg(privileged_reg_t.USTATUS)
        self.ustatus.randomize()
        self.ustatus_set_field(mode, regs)
        self.uie_set_field(mode, regs)

    def gen_csr_instr(self, regs, instrs):
        for i in range(len(regs)):
            instrs.append("li x{}, {}".format(cfg.gpr[0], hex(regs[i].get_val())))
            instrs.append("csrw {}, x{} # {}".format(hex(regs[i].reg_name),
                                                     cfg.gpr[0], regs[i].reg_name.name))

    def setup_satp(self, instrs):
        satp_ppn_mask = vsc.bit_t(rcs.XLEN)
        if rcs.SATP_MODE == satp_mode_t.BARE:
            return
        satp = riscv_privil_reg()
        satp.init_reg(privileged_reg_t.SATP)
        satp.set_field("MODE", rcs.SATP_MODE)
        li0_instr = "li x{}, {}".format(cfg.gpr[0], hex(satp.get_val()))
        csrw_instr = "csrw {}, x{} // satp".format(hex(privileged_reg_t.SATP), cfg.gpr[0])
        fld_name = satp.get_field_by_name("PPN")
        satp_ppn_mask = hex((2**rcs.XLEN) - 1) >> (rcs.XLEN - fld_name.bit_width)
        # Load the root page table physical address
        la_instr = "la x{}, page_table_0".format(cfg.gpr[0])
        # Right shift to get PPN at 4k granularity
        srli_instr = "srli x{}, x{}, 12".format(cfg.gpr[0], cfg.gpr[0])
        li1_instr = "li   x{}, {}".format(cfg.gpr[1], hex(satp_ppn_mask))
        and_instr = "and x{}, x{}, x{}".format(cfg.gpr[0], cfg.gpr[0], cfg.gpr[1])
        # Set the PPN field for SATP
        csrs_instr = "csrs {}, x{} // satp".format(hex(privileged_reg_t.SATP), cfg.gpr[0])
        instrs.extend((li0_instr, csrw_instr, la_instr, srli_instr,
                       li1_instr, and_instr, csrs_instr))

    def mstatus_set_field(self, mode, regs):
        if cfg.randomize_csr:
            self.mstatus.set_val(cfg.mstatus)
        self.mstatus.set_field("MPRV", cfg.mstatus_mprv)
        self.mstatus.set_field("MXR", cfg.mstatus_mxr)
        self.mstatus.set_field("SUM", cfg.mstatus_sum)
        self.mstatus.set_field("TVM", cfg.mstatus_tvm)
        self.mstatus.set_field("TW", cfg.set_mstatus_tw)
        self.mstatus.set_field("FS", cfg.mstatus_fs)
        self.mstatus.set_field("VS", cfg.mstatus_vs)
        if (not(privileged_mode_t.SUPERVISOR_MODE in rcs.supported_privileged_mode) and
                (rcs.XLEN != 32)):
            self.mstatus.set_field("SXL", 0)
        elif rcs.XLEN == 64:
            self.mstatus.set_field("SXL", 2)
        if (not(privileged_mode_t.USER_MODE in rcs.supported_privileged_mode) and (rcs.XLEN != 32)):
            self.mstatus.set_field("UXL", 0)
        elif rcs.XLEN == 64:
            self.mstatus.set_field("UXL", 2)
        self.mstatus.set_field("XS", 0)
        self.mstatus.set_field("SD", 0)
        self.mstatus.set_field("UIE", 0)
        # Set the previous privileged mode as the target mode
        self.mstatus.set_field("MPP", mode.value)
        self.mstatus.set_field("SPP", 0)
        # Enable Interrupt
        self.mstatus.set_field("MPIE", cfg.enable_interrupt)
        self.mstatus.set_field("MIE", cfg.enable_interrupt)
        self.mstatus.set_field("SPIE", cfg.enable_interrupt)
        self.mstatus.set_field("SIE", cfg.enable_interrupt)
        self.mstatus.set_field("UPIE", cfg.enable_interrupt)
        self.mstatus.set_field("UIE", rcs.support_umode_trap)
        logging.info("self.mstatus_val: {}".format(hex(self.mstatus.get_val())))
        regs.append(self.mstatus)

    def sstatus_set_field(self, mode, regs):
        if cfg.randomize_csr:
            self.sstatus.set_val(cfg.sstatus)
        self.sstatus.set_field("SPIE", cfg.enable_interrupt)
        self.sstatus.set_field("SIE", cfg.enable_interrupt)
        self.sstatus.set_field("UPIE", cfg.enable_interrupt)
        self.sstatus.set_field("UIE", rcs.support_umode_trap)
        if rcs.XLEN == 64:
            self.sstatus.set_field("UXL", 2)
        self.sstatus.set_field("FS", cfg.mstatus_fs)
        self.sstatus.set_field("XS", 0)
        self.sstatus.set_field("SD", 0)
        self.sstatus.set_field("UIE", 0)
        self.sstatus.set_field("SPP", 0)
        regs.append(self.sstatus)

    def ustatus_set_field(self, mode, regs):
        if cfg.randomize_csr:
            self.ustatus.set_val(cfg.ustatus)
        self.ustatus.set_field("UIE", cfg.enable_interrupt)
        self.ustatus.set_field("UPIE", cfg.enable_interrupt)
        regs.append(self.ustatus)

    def mie_set_field(self, mode, regs):
        # Enable external and timer interrupt
        if privileged_reg_t.MIE in rcs.implemented_csr:
            self.mie = riscv_privil_reg()
            self.mie.init_reg(privileged_reg_t.MIE)
            if cfg.randomize_csr:
                self.mie.set_val(cfg.mie)
            self.mie.set_field("UEIE", cfg.enable_interrupt)
            self.mie.set_field("SEIE", cfg.enable_interrupt)
            self.mie.set_field("MEIE", cfg.enable_interrupt)
            self.mie.set_field("USIE", cfg.enable_interrupt)
            self.mie.set_field("SSIE", cfg.enable_interrupt)
            self.mie.set_field("MSIE", cfg.enable_interrupt)
            self.mie.set_field("MTIE", cfg.enable_interrupt & cfg.enable_timer_irq)
            self.mie.set_field("STIE", cfg.enable_interrupt & cfg.enable_timer_irq)
            self.mie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq)
            regs.append(self.mie)

    def sie_set_field(self, mode, regs):
        # Enable external and timer interrupt
        if privileged_reg_t.SIE in rcs.implemeted_csr:
            self.sie = riscv_privil_reg()
            self.sie.init_reg(privileged_reg_t.SIE)
            if cfg.randomize_csr:
                self.sie.set_val(cfg.sie)
            self.sie.set_field("UEIE", cfg.enable_interrupt)
            self.sie.set_field("SEIE", cfg.enable_interrupt)
            self.sie.set_field("USIE", cfg.enable_interrupt)
            self.sie.set_field("SSIE", cfg.enable_interrupt)
            self.sie.set_field("STIE", cfg.enable_interrupt & cfg.enable_timer_irq)
            self.sie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq)
            regs.append(self.sie)

    def uie_set_field(self, mode, regs):
        if privileged_reg_t.UIE in rcs.implemented_csr:
            self.uie = riscv_privil_reg()
            self.uie.init_reg(privileged_reg_t.UIE)
            if cfg.randomize_csr:
                self.uie.set_val(cfg.uie)
            self.uie.set_field("UEIE", cfg.enable_interrupt)
            self.uie.set_field("USIE", cfg.enable_interrupt)
            self.uie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq)
            regs.append(self.uie)
