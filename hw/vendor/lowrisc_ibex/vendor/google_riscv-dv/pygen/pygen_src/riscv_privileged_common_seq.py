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
from pygen_src.riscv_instr_pkg import pkg_ins, privileged_reg_t
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_privil_reg import riscv_privil_reg
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


@vsc.randobj
class riscv_privileged_common_seq():
    def __init___(self):
        self.hart = 0
        self.mstatus = vsc.attr(riscv_privil_reg)
        self.mie = vsc.attr(riscv_privil_reg)

    def enter_privileged_mode(self, mode, instrs):
        label = pkg_ins.format_string("{}init_{}:"
                                      .format(pkg_ins.hart_prefix(self.hart), mode),
                                      pkg_ins.LABEL_STR_LEN)
        ret_instr = ["mret"]
        regs = vsc.list_t(vsc.attr(riscv_privil_reg()))
        label = label.lower()
        self.setup_mmode_reg(mode, regs)
        if mode == "SUPERVISOR_MODE":
            self.setup_smode_reg(mode, regs)
        if mode == "USER_MODE":
            self.setup_umode_reg(mode, regs)
        if cfg.virtual_addr_translation_on:
            self.setup_satp(instrs)
        self.gen_csr_instr(regs, instrs)
        # Use mret/sret to switch to the target privileged mode
        instrs.append(ret_instr[0])
        for i in range(len(instrs)):
            instrs[i] = pkg_ins.indent + instrs[i]
        instrs.insert(0, label)

    # TODO
    def setup_mmode_reg(self, mode, regs):
        self.mstatus = riscv_privil_reg()
        self.mstatus.init_reg(privileged_reg_t.MSTATUS)
        if cfg.randomize_csr:
            self.mstatus.set_val(cfg.mstatus)
        self.mstatus.set_field("MPRV", cfg.mstatus_mprv)
        self.mstatus.set_field("MXR", cfg.mstatus_mxr)
        self.mstatus.set_field("SUM", cfg.mstatus_sum)
        self.mstatus.set_field("TVM", cfg.mstatus_tvm)
        self.mstatus.set_field("TW", cfg.set_mstatus_tw)
        self.mstatus.set_field("FS", cfg.mstatus_fs)
        self.mstatus.set_field("VS", cfg.mstatus_vs)
        if (not("SUPERVISOR_MODE" in rcs.supported_privileged_mode) and (rcs.XLEN != 32)):
            self.mstatus.set_field("SXL", 0)
        elif rcs.XLEN == 64:
            self.mstatus.set_field("SXL", 2)
        if (not("USER_MODE" in rcs.supported_privileged_mode) and (rcs.XLEN != 32)):
            self.mstatus.set_field("UXL", 0)
        elif rcs.XLEN == 64:
            self.mstatus.set_field("UXL", 2)
        self.mstatus.set_field("XS", 0)
        self.mstatus.set_field("SD", 0)
        self.mstatus.set_field("UIE", 0)
        # Set the previous privileged mode as the target mode
        self.mstatus.set_field("MPP", 3)  # TODO pass mode value as parameter
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
        # Enable external and timer interrupt
        if "MIE" in rcs.implemented_csr:
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

    # TODO
    def setup_smode_reg(self, mode, regs):
        pass

    # TODO
    def setup_umode_reg(self, mode, regs):
        pass

    # TODO
    def setup_satp(self, instrs):
        pass

    def gen_csr_instr(self, regs, instrs):
        for i in range(len(regs)):
            instrs.append("li x{}, {}".format(cfg.gpr[0].value, hex(regs[i].get_val())))
            instrs.append("csrw {}, x{} # {}".format(hex(regs[i].reg_name.value),
                                                     cfg.gpr[0], regs[i].reg_name.name))
