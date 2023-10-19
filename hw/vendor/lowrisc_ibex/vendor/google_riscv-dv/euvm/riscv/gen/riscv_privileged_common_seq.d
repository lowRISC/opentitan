/*
 * Copyright 2018 Google LLC
 * Copyright 2022 Coverify Systems Technology
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This class provides some common routines for privileged mode operations

module riscv.gen.riscv_privileged_common_seq;

import riscv.gen.riscv_instr_pkg: privileged_mode_t, privileged_reg_t,
  format_string, indent, satp_mode_t, hart_prefix, LABEL_STR_LEN;
import riscv.gen.target: supported_privileged_mode, support_umode_trap,
  implemented_csr, XLEN, SATP_MODE;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import riscv.gen.riscv_privil_reg: riscv_privil_reg;

import std.algorithm.searching: canFind;
import std.format: format;
import std.string: toLower;

import esdl.data.queue: Queue;
import esdl.data.bvec: ubvec, toubvec;
import esdl.rand: randomize;

import uvm;

class riscv_privileged_common_seq : uvm_sequence!(uvm_sequence_item,uvm_sequence_item)
{

  riscv_instr_gen_config  cfg;
  int                     hart;
  riscv_privil_reg        mstatus;
  riscv_privil_reg        mie;
  riscv_privil_reg        sstatus;
  riscv_privil_reg        sie;
  riscv_privil_reg        ustatus;
  riscv_privil_reg        uie;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  void enter_privileged_mode(in privileged_mode_t mode,
			     out Queue!string instrs) {
    import std.conv: to;
    string label = format_string(format("%0sinit_%0s:",
					hart_prefix(hart), mode), LABEL_STR_LEN);
    string[] ret_instr = ["mret"];
    riscv_privil_reg[] regs;
    label = label.toLower();
    setup_mmode_reg(mode, regs);
    if (mode == privileged_mode_t.SUPERVISOR_MODE) {
      setup_smode_reg(mode, regs);
    }
    if (mode == privileged_mode_t.USER_MODE) {
      setup_umode_reg(mode, regs);
    }
    if (cfg.virtual_addr_translation_on) {
      setup_satp(instrs);
    }
    gen_csr_instr(regs, instrs);
    // Use mret/sret to switch to the target privileged mode
    instrs ~= ret_instr[0];
    foreach (instr; instrs) {
      instr = indent ~ instr;
    }
    instrs.pushFront(label);
  }

  void enter_privileged_mode(in privileged_mode_t mode,
			     out string[] instrs) {
    import std.conv: to;
    string label = format_string(format("%0sinit_%0s:",
					hart_prefix(hart), mode), LABEL_STR_LEN);
    string[] ret_instr = ["mret"];
    riscv_privil_reg[] regs;
    label = label.toLower();
    instrs ~= label;
    setup_mmode_reg(mode, regs);
    if (mode == privileged_mode_t.SUPERVISOR_MODE) {
      setup_smode_reg(mode, regs);
    }
    if (mode == privileged_mode_t.USER_MODE) {
      setup_umode_reg(mode, regs);
    }
    if (cfg.virtual_addr_translation_on) {
      setup_satp(instrs);
    }
    gen_csr_instr(regs, instrs);
    // Use mret/sret to switch to the target privileged mode
    instrs ~= ret_instr[0];
    foreach (i, ref instr; instrs) {
      if (i != 0)		// skip indent for label
	instr = indent ~ instr;
    }
    // instrs.pushFront(label); // do it upfront
  }

  void setup_mmode_reg(privileged_mode_t mode, ref riscv_privil_reg[] regs) {
    mstatus = riscv_privil_reg.type_id.create("mstatus");
    mstatus.init_reg(privileged_reg_t.MSTATUS);
    if (cfg.randomize_csr) {
      mstatus.set_val(cfg.mstatus);
    }
    mstatus.set_field("MPRV", cfg.mstatus_mprv);
    mstatus.set_field("MXR", cfg.mstatus_mxr);
    mstatus.set_field("SUM", cfg.mstatus_sum);
    mstatus.set_field("TVM", cfg.mstatus_tvm);
    mstatus.set_field("TW", cfg.set_mstatus_tw);
    mstatus.set_field("FS", cfg.mstatus_fs);
    mstatus.set_field("VS", cfg.mstatus_vs);
    if (XLEN != 32) {
      if (!(canFind(supported_privileged_mode, privileged_mode_t.SUPERVISOR_MODE))) {
        mstatus.set_field("SXL", toubvec!2(0b00));
      }
      else if (XLEN == 64) {
        mstatus.set_field("SXL", toubvec!2(0b10));
      }
      if (!(canFind(supported_privileged_mode, privileged_mode_t.USER_MODE))) {
        mstatus.set_field("UXL", toubvec!2(0b00));
      } else if (XLEN == 64) {
        mstatus.set_field("UXL", toubvec!2(0b10));
      }
    }
    mstatus.set_field("XS", 0);
    mstatus.set_field("SD", 0);
    mstatus.set_field("UIE", 0);
    // Set the previous privileged mode as the target mode
    mstatus.set_field("MPP", mode);
    mstatus.set_field("SPP", 0);
    // Enable interrupt
    mstatus.set_field("MPIE", cfg.enable_interrupt);
    mstatus.set_field("MIE", cfg.enable_interrupt);
    mstatus.set_field("SPIE", cfg.enable_interrupt);
    mstatus.set_field("SIE",  cfg.enable_interrupt);
    mstatus.set_field("UPIE", cfg.enable_interrupt);
    mstatus.set_field("UIE", support_umode_trap);
    uvm_info(get_full_name(), format("mstatus_val: 0x%0x", mstatus.get_val()), UVM_LOW);
    regs ~= mstatus;
    // Enable external and timer interrupt
    if (canFind(implemented_csr, privileged_reg_t.MIE)) {
      mie = riscv_privil_reg.type_id.create("mie");
      mie.init_reg(privileged_reg_t.MIE);
      if (cfg.randomize_csr) {
	mie.set_val(cfg.mie);
      }
      mie.set_field("UEIE", cfg.enable_interrupt);
      mie.set_field("SEIE", cfg.enable_interrupt);
      mie.set_field("MEIE", cfg.enable_interrupt);
      mie.set_field("USIE", cfg.enable_interrupt);
      mie.set_field("SSIE", cfg.enable_interrupt);
      mie.set_field("MSIE", cfg.enable_interrupt);
      mie.set_field("MTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      mie.set_field("STIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      mie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      regs ~= mie;
    }
  }

  void setup_smode_reg(privileged_mode_t mode, ref riscv_privil_reg [] regs) {
    sstatus = riscv_privil_reg.type_id.create("sstatus");
    sstatus.init_reg(privileged_reg_t.SSTATUS);
    sstatus.randomize();
    if (cfg.randomize_csr) {
      sstatus.set_val(cfg.sstatus);
    }
    sstatus.set_field("SPIE", cfg.enable_interrupt);
    sstatus.set_field("SIE",  cfg.enable_interrupt);
    sstatus.set_field("UPIE", cfg.enable_interrupt);
    sstatus.set_field("UIE", support_umode_trap);
    if(XLEN==64) {
      sstatus.set_field("UXL", toubvec!2(0b10));
    }
    sstatus.set_field("FS", cfg.mstatus_fs);
    sstatus.set_field("XS", 0);
    sstatus.set_field("SD", 0);
    sstatus.set_field("UIE", 0);
    sstatus.set_field("SPP", 0);
    regs ~= sstatus;
    // Enable external and timer interrupt
    if (canFind(implemented_csr, privileged_reg_t.SIE)) {
      sie = riscv_privil_reg.type_id.create("sie");
      sie.init_reg(privileged_reg_t.SIE);
      if (cfg.randomize_csr) {
        sie.set_val(cfg.sie);
      }
      sie.set_field("UEIE", cfg.enable_interrupt);
      sie.set_field("SEIE", cfg.enable_interrupt);
      sie.set_field("USIE", cfg.enable_interrupt);
      sie.set_field("SSIE", cfg.enable_interrupt);
      sie.set_field("STIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      sie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      regs ~= sie;
    }
  }

  void setup_umode_reg(privileged_mode_t mode, ref riscv_privil_reg[] regs) {
    // For implementations that do not provide any U-mode CSRs, return immediately
    if (! support_umode_trap) {
      return;
    }
    else {
      ustatus = riscv_privil_reg.type_id.create("ustatus");
      ustatus.init_reg(privileged_reg_t.USTATUS);
      ustatus.randomize();
      if (cfg.randomize_csr) {
	ustatus.set_val(cfg.ustatus);
      }
      ustatus.set_field("UIE", cfg.enable_interrupt);
      ustatus.set_field("UPIE", cfg.enable_interrupt);
      regs ~= ustatus;
      if (canFind(implemented_csr, privileged_reg_t.UIE )) {
	uie = riscv_privil_reg.type_id.create("uie");
	uie.init_reg(privileged_reg_t.UIE);
	if (cfg.randomize_csr) {
	  uie.set_val(cfg.uie);
	}
	uie.set_field("UEIE", cfg.enable_interrupt);
	uie.set_field("USIE", cfg.enable_interrupt);
	uie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
	regs ~= uie;
      }
    }
  }

  void gen_csr_instr(riscv_privil_reg[] regs, ref Queue!string instrs) {
    import std.conv: to;
    foreach (r; regs) {
      instrs ~= format("li x%0d, 0x%0x", cfg.gpr[0], r.get_val());
      instrs ~= format("csrw 0x%0x, x%0d # %0s",
		       r.reg_name, cfg.gpr[0], r.reg_name.to!string());
    }
  }

  void gen_csr_instr(riscv_privil_reg[] regs, ref string[] instrs) {
    import std.conv: to;
    foreach (r; regs) {
      instrs ~= format("li x%0d, 0x%0x", cfg.gpr[0], r.get_val());
      instrs ~= format("csrw 0x%0x, x%0d # %0s",
		       r.reg_name, cfg.gpr[0], r.reg_name.to!string());
    }
  }

  void setup_satp(ref Queue!string instrs) {
    riscv_privil_reg satp;
    ubvec!XLEN satp_ppn_mask;
    if (SATP_MODE == satp_mode_t.BARE) return;
    else {
      satp = riscv_privil_reg.type_id.create("satp");
      satp.init_reg(privileged_reg_t.SATP);
      satp.set_field("MODE", SATP_MODE);
      instrs ~= format("li x%0d, 0x%0x", cfg.gpr[0], satp.get_val());
      instrs ~= format("csrw 0x%0x, x%0d # satp", privileged_reg_t.SATP, cfg.gpr[0]);
      satp_ppn_mask = ubvec!XLEN.max >> (XLEN - satp.get_field_by_name("PPN").bit_width);
      // Load the root page table physical address
      instrs ~= format("la x%0d, page_table_0", cfg.gpr[0]);
      // Right shift to get PPN at 4k granularity
      instrs ~= format("srli x%0d, x%0d, 12", cfg.gpr[0], cfg.gpr[0]);
      instrs ~= format("li   x%0d, 0x%0x", cfg.gpr[1], satp_ppn_mask);
      instrs ~= format("and x%0d, x%0d, x%0d", cfg.gpr[0], cfg.gpr[0], cfg.gpr[1]);
      // Set the PPN field for SATP
      instrs ~= format("csrs 0x%0x, x%0d # satp", privileged_reg_t.SATP, cfg.gpr[0]);
    }
  }

  void setup_satp(ref string[] instrs) {
    riscv_privil_reg satp;
    ubvec!XLEN satp_ppn_mask;
    if (SATP_MODE == satp_mode_t.BARE) return;
    else {
      satp = riscv_privil_reg.type_id.create("satp");
      satp.init_reg(privileged_reg_t.SATP);
      satp.set_field("MODE", SATP_MODE);
      instrs ~= format("li x%0d, 0x%0x", cfg.gpr[0], satp.get_val());
      instrs ~= format("csrw 0x%0x, x%0d # satp", privileged_reg_t.SATP, cfg.gpr[0]);
      satp_ppn_mask = ubvec!XLEN.max >> (XLEN - satp.get_field_by_name("PPN").bit_width);
      // Load the root page table physical address
      instrs ~= format("la x%0d, page_table_0", cfg.gpr[0]);
      // Right shift to get PPN at 4k granularity
      instrs ~= format("srli x%0d, x%0d, 12", cfg.gpr[0], cfg.gpr[0]);
      instrs ~= format("li   x%0d, 0x%0x", cfg.gpr[1], satp_ppn_mask);
      instrs ~= format("and x%0d, x%0d, x%0d", cfg.gpr[0], cfg.gpr[0], cfg.gpr[1]);
      // Set the PPN field for SATP
      instrs ~= format("csrs 0x%0x, x%0d # satp", privileged_reg_t.SATP, cfg.gpr[0]);
    }
  }

}
