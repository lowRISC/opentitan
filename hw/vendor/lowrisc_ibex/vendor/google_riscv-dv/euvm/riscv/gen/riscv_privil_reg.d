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

// RISC-V privileged register class

module riscv.gen.riscv_privil_reg;

import riscv.gen.riscv_instr_pkg: privileged_reg_t, privileged_level_t,
  reg_field_access_t;
import riscv.gen.target: XLEN;
import riscv.gen.riscv_reg: riscv_reg;
import std.format: format;

import uvm;

class riscv_privil_reg: riscv_reg!(privileged_reg_t)
{

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override void init_reg(privileged_reg_t reg_name) {
    super.init_reg(reg_name);
    switch(reg_name) {
      /////////////// Machine mode reigster //////////////
      // Machine ISA Register
    case privileged_reg_t.MISA:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("WARL0", 26, reg_field_access_t.WARL);
      add_field("WLRL", XLEN-28, reg_field_access_t.WLRL);
      add_field("MXL", 2, reg_field_access_t.WARL);
      break;
      // Machine Vendor ID Register
    case privileged_reg_t.MVENDORID:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("OFFSET", 7, reg_field_access_t.WPRI);
      add_field("BANK", XLEN-7, reg_field_access_t.WPRI);
      break;
      // Machine Architecture ID Register
    case privileged_reg_t.MARCHID:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("ARCHITECTURE_ID", XLEN, reg_field_access_t.WPRI);
      break;
      // Machine Implementation ID Register
    case privileged_reg_t.MIMPID:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("IMPLEMENTATION", XLEN, reg_field_access_t.WPRI);
      break;
      // Hart ID Register
    case privileged_reg_t.MHARTID:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("HART_ID", XLEN, reg_field_access_t.WPRI);
      break;
      // Machine Status Register
    case privileged_reg_t.MSTATUS:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("UIE",   1,  reg_field_access_t.WARL);
      add_field("SIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI0", 1,  reg_field_access_t.WPRI);
      add_field("MIE",   1,  reg_field_access_t.WARL);
      add_field("UPIE",  1,  reg_field_access_t.WARL);
      add_field("SPIE",  1,  reg_field_access_t.WARL);
      add_field("WPRI1", 1,  reg_field_access_t.WPRI);
      add_field("MPIE",  1,  reg_field_access_t.WARL);
      add_field("SPP",   1,  reg_field_access_t.WLRL);
      add_field("VS",    2,  reg_field_access_t.WARL);
      add_field("MPP",   2,  reg_field_access_t.WLRL);
      add_field("FS",    2,  reg_field_access_t.WARL);
      add_field("XS",    2,  reg_field_access_t.WARL);
      add_field("MPRV",  1,  reg_field_access_t.WARL);
      add_field("SUM",   1,  reg_field_access_t.WARL);
      add_field("MXR",   1,  reg_field_access_t.WARL);
      add_field("TVM",   1,  reg_field_access_t.WARL);
      add_field("TW",    1,  reg_field_access_t.WARL);
      add_field("TSR",   1,  reg_field_access_t.WARL);
      if (XLEN == 32) {
	add_field("WPRI3", 8,  reg_field_access_t.WPRI);
      }
      else {
	add_field("WPRI3", 9,  reg_field_access_t.WPRI);
	add_field("UXL",   2,  reg_field_access_t.WARL);
	add_field("SXL",   2,  reg_field_access_t.WARL);
	add_field("WPRI4", XLEN - 37, reg_field_access_t.WPRI);
      }
      add_field("SD",   1,  reg_field_access_t.WARL);
      break;
      // Machine Trap-Vector Base-Address Register
    case privileged_reg_t.MTVEC:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("MODE",  2,  reg_field_access_t.WARL);
      add_field("BASE",  XLEN - 2,  reg_field_access_t.WARL);
      break;
      // Machine Exception Delegation Register
    case privileged_reg_t.MEDELEG:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("IAM", 1, reg_field_access_t.WARL);
      add_field("IAF", 1, reg_field_access_t.WARL);
      add_field("ILGL", 1, reg_field_access_t.WARL);
      add_field("BREAK", 1, reg_field_access_t.WARL);
      add_field("LAM", 1, reg_field_access_t.WARL);
      add_field("LAF", 1, reg_field_access_t.WARL);
      add_field("SAM", 1, reg_field_access_t.WARL);
      add_field("SAF", 1, reg_field_access_t.WARL);
      add_field("ECFU", 1, reg_field_access_t.WARL);
      add_field("ECFS", 1, reg_field_access_t.WARL);
      add_field("WARL0", 1, reg_field_access_t.WARL);
      add_field("ECFM", 1, reg_field_access_t.WARL);
      add_field("IPF", 1, reg_field_access_t.WARL);
      add_field("LPF", 1, reg_field_access_t.WARL);
      add_field("WARL1", 1, reg_field_access_t.WARL);
      add_field("SPF", 1, reg_field_access_t.WARL);
      add_field("WARL2", XLEN-16, reg_field_access_t.WARL);
      break;

      // Machine Interrupt Delegation Register
    case privileged_reg_t.MIDELEG:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("USIP", 1, reg_field_access_t.WARL);
      add_field("SSIP", 1, reg_field_access_t.WARL);
      add_field("WARL0", 1, reg_field_access_t.WARL);
      add_field("MSIP", 1, reg_field_access_t.WARL);
      add_field("UTIP", 1, reg_field_access_t.WARL);
      add_field("STIP", 1, reg_field_access_t.WARL);
      add_field("WARL1", 1, reg_field_access_t.WARL);
      add_field("MTIP", 1, reg_field_access_t.WARL);
      add_field("UEIP", 1, reg_field_access_t.WARL);
      add_field("SEIP", 1, reg_field_access_t.WARL);
      add_field("WARL2", 1, reg_field_access_t.WARL);
      add_field("MEIP", 1, reg_field_access_t.WARL);
      add_field("WARL3", XLEN-12, reg_field_access_t.WARL);
      break;
      // Machine trap-enable register
    case privileged_reg_t.MIP:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("USIP",   1,  reg_field_access_t.WARL);
      add_field("SSIP",   1,  reg_field_access_t.WARL);
      add_field("WPRI0",  1,  reg_field_access_t.WPRI);
      add_field("MSIP",   1,  reg_field_access_t.WARL);
      add_field("UTIP",   1,  reg_field_access_t.WARL);
      add_field("STIP",   1,  reg_field_access_t.WARL);
      add_field("WPRI1",  1,  reg_field_access_t.WPRI);
      add_field("MTIP",   1,  reg_field_access_t.WARL);
      add_field("UEIP",   1,  reg_field_access_t.WARL);
      add_field("SEIP",   1,  reg_field_access_t.WARL);
      add_field("WPRI2",  1,  reg_field_access_t.WPRI);
      add_field("MEIP",   1,  reg_field_access_t.WARL);
      add_field("WPRI3",  XLEN - 12,  reg_field_access_t.WPRI);
      break;

      // Machine Interrupt-enable register
    case privileged_reg_t.MIE:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("USIE",   1,  reg_field_access_t.WARL);
      add_field("SSIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI0",  1,  reg_field_access_t.WPRI);
      add_field("MSIE",   1,  reg_field_access_t.WARL);
      add_field("UTIE",   1,  reg_field_access_t.WARL);
      add_field("STIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI1",  1,  reg_field_access_t.WPRI);
      add_field("MTIE",   1,  reg_field_access_t.WARL);
      add_field("UEIE",   1,  reg_field_access_t.WARL);
      add_field("SEIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI2",  1,  reg_field_access_t.WPRI);
      add_field("MEIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI3",  XLEN - 12,  reg_field_access_t.WPRI);
      break;
      // Cycle Count Register
    case privileged_reg_t.MCYCLE:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("MCYCLE", 64, reg_field_access_t.WPRI);
      break;
      // Instruction Count Register
    case privileged_reg_t.MINSTRET:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("MINSTRET", 64, reg_field_access_t.WPRI);
      break;
      // Cycle Count Register - RV32I only
    case privileged_reg_t.MCYCLEH:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("MCYCLEH", 32, reg_field_access_t.WPRI);
      break;
      // Instruction Count Register - RV32I only
    case privileged_reg_t.MINSTRETH:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("MINSTRETH", 32, reg_field_access_t.WPRI);
      break;
      // Hardware Performance Monitor Counters
    case privileged_reg_t.MHPMCOUNTER3:
      ..
    case privileged_reg_t.MHPMCOUNTER31:
      privil_level = privileged_level_t.M_LEVEL;
      add_field(format("%s", reg_name), XLEN, reg_field_access_t.WARL);
      break;
      // Hardware Performance Monitor Events
    case privileged_reg_t.MHPMEVENT3:
      ..
    case privileged_reg_t.MHPMEVENT31:
      privil_level = privileged_level_t.M_LEVEL;
      add_field(format("%s", reg_name), XLEN, reg_field_access_t.WARL);
      break;

      // Hardware Performance Monitor Counters - RV32I only
    case  privileged_reg_t.MHPMCOUNTER3H:
      ..
    case privileged_reg_t.MHPMCOUNTER31H:
      if (XLEN != 32) {
	uvm_fatal(get_full_name(), format("Register %s is only in RV32I", reg_name));
      }
      privil_level = privileged_level_t.M_LEVEL;
      add_field(format("%s", reg_name), 32, reg_field_access_t.WARL);
      break;
      // Machine Counter Enable Register
    case privileged_reg_t.MCOUNTEREN:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("CY", 1, reg_field_access_t.WARL);
      add_field("TM", 1, reg_field_access_t.WARL);
      add_field("IR", 1, reg_field_access_t.WARL);
      add_field("HPM3", 1, reg_field_access_t.WARL);
      add_field("HPM4", 1, reg_field_access_t.WARL);
      add_field("HPM5", 1, reg_field_access_t.WARL);
      add_field("HPM6", 1, reg_field_access_t.WARL);
      add_field("HPM7", 1, reg_field_access_t.WARL);
      add_field("HPM8", 1, reg_field_access_t.WARL);
      add_field("HPM9", 1, reg_field_access_t.WARL);
      add_field("HPM10", 1, reg_field_access_t.WARL);
      add_field("HPM11", 1, reg_field_access_t.WARL);
      add_field("HPM12", 1, reg_field_access_t.WARL);
      add_field("HPM13", 1, reg_field_access_t.WARL);
      add_field("HPM14", 1, reg_field_access_t.WARL);
      add_field("HPM15", 1, reg_field_access_t.WARL);
      add_field("HPM16", 1, reg_field_access_t.WARL);
      add_field("HPM17", 1, reg_field_access_t.WARL);
      add_field("HPM18", 1, reg_field_access_t.WARL);
      add_field("HPM19", 1, reg_field_access_t.WARL);
      add_field("HPM20", 1, reg_field_access_t.WARL);
      add_field("HPM21", 1, reg_field_access_t.WARL);
      add_field("HPM22", 1, reg_field_access_t.WARL);
      add_field("HPM23", 1, reg_field_access_t.WARL);
      add_field("HPM24", 1, reg_field_access_t.WARL);
      add_field("HPM25", 1, reg_field_access_t.WARL);
      add_field("HPM26", 1, reg_field_access_t.WARL);
      add_field("HPM27", 1, reg_field_access_t.WARL);
      add_field("HPM28", 1, reg_field_access_t.WARL);
      add_field("HPM29", 1, reg_field_access_t.WARL);
      add_field("HPM30", 1, reg_field_access_t.WARL);
      add_field("HPM31", 1, reg_field_access_t.WARL);
      if (XLEN == 64) {
	add_field("reg_field_access_t.WPRI",  32,  reg_field_access_t.WPRI);
      }
      break;
      // Machine Scratch Register
    case privileged_reg_t.MSCRATCH:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("MSCRATCH", XLEN, reg_field_access_t.WARL);
      break;
      // Machine Exception Program Counter
    case privileged_reg_t.MEPC:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("BASE",  XLEN,  reg_field_access_t.WARL);
      break;
      // Machine Cause Register
    case privileged_reg_t.MCAUSE:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("CODE",  4,  reg_field_access_t.WLRL);
      add_field("WLRL", XLEN-5, reg_field_access_t.WLRL);
      add_field("INTERRUPT",  1,  reg_field_access_t.WARL);
      break;
      // Machine Trap Value
    case privileged_reg_t.MTVAL:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("VALUE",  XLEN,  reg_field_access_t.WARL);
      break;
      // Physical Memory Protection Configuration Register
    case privileged_reg_t.PMPCFG0:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("PMP0CFG", 8, reg_field_access_t.WARL);
      add_field("PMP1CFG", 8, reg_field_access_t.WARL);
      add_field("PMP2CFG", 8, reg_field_access_t.WARL);
      add_field("PMP3CFG", 8, reg_field_access_t.WARL);
      if (XLEN==64) {
	add_field("PMP4CFG", 8, reg_field_access_t.WARL);
	add_field("PMP5CFG", 8, reg_field_access_t.WARL);
	add_field("PMP6CFG", 8, reg_field_access_t.WARL);
	add_field("PMP7CFG", 8, reg_field_access_t.WARL);
      }
      break;
      // Physical Memory Protection Configuration Register
    case  privileged_reg_t.PMPCFG1:
      privil_level = privileged_level_t.M_LEVEL;
      if (XLEN!=32) {
	uvm_fatal(get_full_name(), "CSR PMPCFG1 only exists in RV32.");
      }
      else {
	add_field("PMP4CFG", 8, reg_field_access_t.WARL);
	add_field("PMP5CFG", 8, reg_field_access_t.WARL);
	add_field("PMP6CFG", 8, reg_field_access_t.WARL);
	add_field("PMP7CFG", 8, reg_field_access_t.WARL);
      }
      break;
      // Physical Memory Protection Configuration Register
    case privileged_reg_t.PMPCFG2:
      privil_level = privileged_level_t.M_LEVEL;
      add_field("PMP8CFG", 8, reg_field_access_t.WARL);
      add_field("PMP9CFG", 8, reg_field_access_t.WARL);
      add_field("PMP10CFG", 8, reg_field_access_t.WARL);
      add_field("PMP11CFG", 8, reg_field_access_t.WARL);
      if (XLEN==64) {
	add_field("PMP12CFG", 8, reg_field_access_t.WARL);
	add_field("PMP13CFG", 8, reg_field_access_t.WARL);
	add_field("PMP14CFG", 8, reg_field_access_t.WARL);
	add_field("PMP15CFG", 8, reg_field_access_t.WARL);
      }
      break;
      // Physical Memory Protection Configuration Register
    case privileged_reg_t.PMPCFG3:
      if (XLEN!=32) {
	uvm_fatal(get_full_name(), "CSR PMPCFG3 only exists in RV32.");
      }
      privil_level = privileged_level_t.M_LEVEL;
      add_field("PMP12CFG", 8, reg_field_access_t.WARL);
      add_field("PMP13CFG", 8, reg_field_access_t.WARL);
      add_field("PMP14CFG", 8, reg_field_access_t.WARL);
      add_field("PMP15CFG", 8, reg_field_access_t.WARL);
      break;
      // Physical Memory Protection Configuration Registers
    case privileged_reg_t.PMPADDR0:
      ..
    case privileged_reg_t.PMPADDR15:
      privil_level = privileged_level_t.M_LEVEL;
      if (XLEN==64) {
	add_field("ADDRESS", 54, reg_field_access_t.WARL);
	add_field("WARL", 10, reg_field_access_t.WARL);
      }
      else {
	add_field("ADDRESS", 32, reg_field_access_t.WARL);
      }
      break;
      /////////////// Supervisor mode reigster //////////////
      // Supervisor status register
    case privileged_reg_t.SSTATUS:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("UIE",   1,  reg_field_access_t.WARL);
      add_field("SIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI0", 2,  reg_field_access_t.WPRI);
      add_field("UPIE",  1,  reg_field_access_t.WARL);
      add_field("SPIE",  1,  reg_field_access_t.WARL);
      add_field("WPRI1", 2,  reg_field_access_t.WPRI);
      add_field("SPP",   1,  reg_field_access_t.WLRL);
      add_field("WPRI2", 4,  reg_field_access_t.WPRI);
      add_field("FS",    2,  reg_field_access_t.WARL);
      add_field("XS",    2,  reg_field_access_t.WARL);
      add_field("WPRI3", 1,  reg_field_access_t.WPRI);
      add_field("SUM",   1,  reg_field_access_t.WARL);
      add_field("MXR",   1,  reg_field_access_t.WARL);
      if (XLEN == 32) {
	add_field("WPRI4", 11,  reg_field_access_t.WPRI);
      } else {
	add_field("WPRI4", 12,  reg_field_access_t.WPRI);
	add_field("UXL",   2,  reg_field_access_t.WARL);
	add_field("WPRI4", XLEN - 35, reg_field_access_t.WPRI);
      }
      add_field("SD",   1,  reg_field_access_t.WARL);
      break;
      // Supervisor Trap Vector Base Address Register
    case privileged_reg_t.STVEC:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("MODE", 2, reg_field_access_t.WARL);
      add_field("BASE", XLEN-2, reg_field_access_t.WLRL);
      break;
      // Supervisor Exception Delegation Register
    case privileged_reg_t.SEDELEG:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("IAM", 1, reg_field_access_t.WARL);
      add_field("IAF", 1, reg_field_access_t.WARL);
      add_field("II", 1, reg_field_access_t.WARL);
      add_field("WPRI0", 1, reg_field_access_t.WPRI);
      add_field("LAM", 1, reg_field_access_t.WARL);
      add_field("LAF", 1, reg_field_access_t.WARL);
      add_field("SAM", 1, reg_field_access_t.WARL);
      add_field("SAF", 1, reg_field_access_t.WARL);
      add_field("ECFU", 1, reg_field_access_t.WARL);
      add_field("WPRI1", 1, reg_field_access_t.WPRI);
      add_field("WARL0", 1, reg_field_access_t.WARL);
      add_field("WPRI2", 1, reg_field_access_t.WPRI);
      add_field("IPF", 1, reg_field_access_t.WARL);
      add_field("LPF", 1, reg_field_access_t.WARL);
      add_field("WARL1", 1, reg_field_access_t.WARL);
      add_field("SPF", 1, reg_field_access_t.WARL);
      add_field("WARL2", XLEN-16, reg_field_access_t.WARL);
      break;
      // Supervisor Interrupt Delegation Register
    case privileged_reg_t.SIDELEG:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("USIP", 1, reg_field_access_t.WARL);
      add_field("SSIP", 1, reg_field_access_t.WARL);
      add_field("WARL0", 1, reg_field_access_t.WARL);
      add_field("WPRI0", 1, reg_field_access_t.WPRI);
      add_field("UTIP", 1, reg_field_access_t.WARL);
      add_field("STIP", 1, reg_field_access_t.WARL);
      add_field("WARL1", 1, reg_field_access_t.WARL);
      add_field("WPRI1", 1, reg_field_access_t.WPRI);
      add_field("UEIP", 1, reg_field_access_t.WARL);
      add_field("SEIP", 1, reg_field_access_t.WARL);
      add_field("WARL2", 1, reg_field_access_t.WARL);
      add_field("WPRI2", 1, reg_field_access_t.WPRI);
      add_field("WARL3", XLEN-12, reg_field_access_t.WARL);
      break;
      // Supervisor trap-enable register
    case privileged_reg_t.SIP:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("USIP",   1,  reg_field_access_t.WARL);
      add_field("SSIP",   1,  reg_field_access_t.WARL);
      add_field("WPRI0",  2,  reg_field_access_t.WPRI);
      add_field("UTIP",   1,  reg_field_access_t.WARL);
      add_field("STIP",   1,  reg_field_access_t.WARL);
      add_field("WPRI1",  2,  reg_field_access_t.WPRI);
      add_field("UEIP",   1,  reg_field_access_t.WARL);
      add_field("SEIP",   1,  reg_field_access_t.WARL);
      add_field("WPRI2", 2, reg_field_access_t.WPRI);
      add_field("WPRI3",  XLEN - 12,  reg_field_access_t.WPRI);
      break;
      // Supervisor interrupt-enable register
    case privileged_reg_t.SIE:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("USIE",   1,  reg_field_access_t.WARL);
      add_field("SSIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI0",  2,  reg_field_access_t.WPRI);
      add_field("UTIE",   1,  reg_field_access_t.WARL);
      add_field("STIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI1",  2,  reg_field_access_t.WPRI);
      add_field("UEIE",   1,  reg_field_access_t.WARL);
      add_field("SEIE",   1,  reg_field_access_t.WARL);
      add_field("WPRI2",  XLEN - 10,  reg_field_access_t.WPRI);
      break;
      // Supervisor Counter Enable Register
    case privileged_reg_t.SCOUNTEREN:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("CY", 1, reg_field_access_t.WARL);
      add_field("TM", 1, reg_field_access_t.WARL);
      add_field("IR", 1, reg_field_access_t.WARL);
      add_field("HPM3", 1, reg_field_access_t.WARL);
      add_field("HPM4", 1, reg_field_access_t.WARL);
      add_field("HPM5", 1, reg_field_access_t.WARL);
      add_field("HPM6", 1, reg_field_access_t.WARL);
      add_field("HPM7", 1, reg_field_access_t.WARL);
      add_field("HPM8", 1, reg_field_access_t.WARL);
      add_field("HPM9", 1, reg_field_access_t.WARL);
      add_field("HPM10", 1, reg_field_access_t.WARL);
      add_field("HPM11", 1, reg_field_access_t.WARL);
      add_field("HPM12", 1, reg_field_access_t.WARL);
      add_field("HPM13", 1, reg_field_access_t.WARL);
      add_field("HPM14", 1, reg_field_access_t.WARL);
      add_field("HPM15", 1, reg_field_access_t.WARL);
      add_field("HPM16", 1, reg_field_access_t.WARL);
      add_field("HPM17", 1, reg_field_access_t.WARL);
      add_field("HPM18", 1, reg_field_access_t.WARL);
      add_field("HPM19", 1, reg_field_access_t.WARL);
      add_field("HPM20", 1, reg_field_access_t.WARL);
      add_field("HPM21", 1, reg_field_access_t.WARL);
      add_field("HPM22", 1, reg_field_access_t.WARL);
      add_field("HPM23", 1, reg_field_access_t.WARL);
      add_field("HPM24", 1, reg_field_access_t.WARL);
      add_field("HPM25", 1, reg_field_access_t.WARL);
      add_field("HPM26", 1, reg_field_access_t.WARL);
      add_field("HPM27", 1, reg_field_access_t.WARL);
      add_field("HPM28", 1, reg_field_access_t.WARL);
      add_field("HPM29", 1, reg_field_access_t.WARL);
      add_field("HPM30", 1, reg_field_access_t.WARL);
      add_field("HPM31", 1, reg_field_access_t.WARL);
      if (XLEN == 64) {
	add_field("reg_field_access_t.WPRI",  32,  reg_field_access_t.WPRI);
      }
      break;
      // Supervisor Scratch Register
    case privileged_reg_t.SSCRATCH:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("SSCRATCH", XLEN, reg_field_access_t.WARL);
      break;
      // Supervisor Exception Program Counter
    case privileged_reg_t.SEPC:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("BASE",  XLEN,  reg_field_access_t.WARL);
      break;
      // Supervisor Cause Register
    case privileged_reg_t.SCAUSE:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("CODE",  4,  reg_field_access_t.WLRL);
      add_field("WLRL", XLEN-5, reg_field_access_t.WLRL);
      add_field("INTERRUPT",  1,  reg_field_access_t.WARL);
      break;
      // Supervisor Trap Value
    case privileged_reg_t.STVAL:
      privil_level = privileged_level_t.S_LEVEL;
      add_field("VALUE",  XLEN,  reg_field_access_t.WARL);
      break;
      // Supervisor Address Translation and Protection
    case privileged_reg_t.SATP:
      privil_level = privileged_level_t.S_LEVEL;
      if (XLEN == 32) {
	add_field("PPN",  22, reg_field_access_t.WARL);
	add_field("ASID", 9,  reg_field_access_t.WARL);
	add_field("MODE", 1,  reg_field_access_t.WARL);
      }
      else {
	add_field("PPN",  44, reg_field_access_t.WARL);
	add_field("ASID", 16, reg_field_access_t.WARL);
	add_field("MODE", 4,  reg_field_access_t.WARL);
      }
      break;
      /////////////// User mode reigster //////////////
      // User Status Register
    case privileged_reg_t.USTATUS:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("UIE", 1, reg_field_access_t.WARL);
      add_field("WPRI0", 3, reg_field_access_t.WPRI);
      add_field("UPIE", 1, reg_field_access_t.WARL);
      add_field("WPRI1", XLEN-5, reg_field_access_t.WPRI);
      break;
      // User Trap Vector Base Address Register
    case privileged_reg_t.UTVEC:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("MODE", 2, reg_field_access_t.WARL);
      add_field("BASE", XLEN-2, reg_field_access_t.WLRL);
      break;
      // User Interrupt-Enable register
    case privileged_reg_t.UIE:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("USIE", 1, reg_field_access_t.WARL);
      add_field("WPRI0", 3, reg_field_access_t.WPRI);
      add_field("UTIE", 1, reg_field_access_t.WARL);
      add_field("WPRI1", 3, reg_field_access_t.WPRI);
      add_field("UEIE", 1, reg_field_access_t.WARL);
      add_field("WPRI2", XLEN-9, reg_field_access_t.WPRI);
      break;
      // User Trap-Enable register
    case privileged_reg_t.UIP:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("USIP", 1, reg_field_access_t.WARL);
      add_field("WPRI0", 3, reg_field_access_t.WPRI);
      add_field("UTIP", 1, reg_field_access_t.WARL);
      add_field("WPRI1", 3, reg_field_access_t.WPRI);
      add_field("UEIP", 1, reg_field_access_t.WARL);
      add_field("WPRI2", XLEN-9, reg_field_access_t.WPRI);
      break;
      // User Scratch Register
    case privileged_reg_t.USCRATCH:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("MSCRATCH", XLEN, reg_field_access_t.WARL);
      break;
      // User Exception Program Counter
    case privileged_reg_t.UEPC:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("BASE",  XLEN,  reg_field_access_t.WARL);
      break;
      // User Cause Register
    case privileged_reg_t.UCAUSE:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("CODE",  4,  reg_field_access_t.WLRL);
      add_field("WLRL", XLEN-5, reg_field_access_t.WLRL);
      add_field("INTERRUPT",  1,  reg_field_access_t.WARL);
      break;
      // User Trap Value
    case privileged_reg_t.UTVAL:
      privil_level = privileged_level_t.U_LEVEL;
      add_field("VALUE",  XLEN,  reg_field_access_t.WARL);
      break;
    default:
      uvm_fatal(get_full_name(), format("reg %0s is not supported yet", reg_name));
    }
  }

}
