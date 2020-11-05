/*
 * Copyright 2018 Google LLC
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
class riscv_privil_reg extends riscv_reg#(privileged_reg_t);

  `uvm_object_utils(riscv_privil_reg)

  function new(string name = "");
    super.new(name);
  endfunction

  function void init_reg(REG_T reg_name);
    super.init_reg(reg_name);
    case(reg_name) inside
      /////////////// Machine mode reigster //////////////
      // Machine ISA Register
      MISA: begin
        privil_level = M_LEVEL;
        add_field("WARL0", 26, WARL);
        add_field("WLRL", XLEN-28, WLRL);
        add_field("MXL", 2, WARL);
      end
      // Machine Vendor ID Register
      MVENDORID: begin
        privil_level = M_LEVEL;
        add_field("OFFSET", 7, WPRI);
        add_field("BANK", XLEN-7, WPRI);
      end
      // Machine Architecture ID Register
      MARCHID: begin
        privil_level = M_LEVEL;
        add_field("ARCHITECTURE_ID", XLEN, WPRI);
      end
      // Machine Implementation ID Register
      MIMPID: begin
        privil_level = M_LEVEL;
        add_field("IMPLEMENTATION", XLEN, WPRI);
      end
      // Hart ID Register
      MHARTID: begin
        privil_level = M_LEVEL;
        add_field("HART_ID", XLEN, WPRI);
      end
      // Machine Status Register
      MSTATUS: begin
        privil_level = M_LEVEL;
        add_field("UIE",   1,  WARL);
        add_field("SIE",   1,  WARL);
        add_field("WPRI0", 1,  WPRI);
        add_field("MIE",   1,  WARL);
        add_field("UPIE",  1,  WARL);
        add_field("SPIE",  1,  WARL);
        add_field("WPRI1", 1,  WPRI);
        add_field("MPIE",  1,  WARL);
        add_field("SPP",   1,  WLRL);
        add_field("VS",    2,  WARL);
        add_field("MPP",   2,  WLRL);
        add_field("FS",    2,  WARL);
        add_field("XS",    2,  WARL);
        add_field("MPRV",  1,  WARL);
        add_field("SUM",   1,  WARL);
        add_field("MXR",   1,  WARL);
        add_field("TVM",   1,  WARL);
        add_field("TW",    1,  WARL);
        add_field("TSR",   1,  WARL);
        if(XLEN == 32) begin
          add_field("WPRI3", 8,  WPRI);
        end else begin
          add_field("WPRI3", 9,  WPRI);
          add_field("UXL",   2,  WARL);
          add_field("SXL",   2,  WARL);
          add_field("WPRI4", XLEN - 37, WPRI);
        end
        add_field("SD",   1,  WARL);
      end
      // Machine Trap-Vector Base-Address Register
      MTVEC: begin
        privil_level = M_LEVEL;
        add_field("MODE",  2,  WARL);
        add_field("BASE",  XLEN - 2,  WARL);
      end
      // Machine Exception Delegation Register
      MEDELEG: begin
        privil_level = M_LEVEL;
        add_field("IAM", 1, WARL);
        add_field("IAF", 1, WARL);
        add_field("ILGL", 1, WARL);
        add_field("BREAK", 1, WARL);
        add_field("LAM", 1, WARL);
        add_field("LAF", 1, WARL);
        add_field("SAM", 1, WARL);
        add_field("SAF", 1, WARL);
        add_field("ECFU", 1, WARL);
        add_field("ECFS", 1, WARL);
        add_field("WARL0", 1, WARL);
        add_field("ECFM", 1, WARL);
        add_field("IPF", 1, WARL);
        add_field("LPF", 1, WARL);
        add_field("WARL1", 1, WARL);
        add_field("SPF", 1, WARL);
        add_field("WARL2", XLEN-16, WARL);
      end
      // Machine Interrupt Delegation Register
      MIDELEG: begin
        privil_level = M_LEVEL;
        add_field("USIP", 1, WARL);
        add_field("SSIP", 1, WARL);
        add_field("WARL0", 1, WARL);
        add_field("MSIP", 1, WARL);
        add_field("UTIP", 1, WARL);
        add_field("STIP", 1, WARL);
        add_field("WARL1", 1, WARL);
        add_field("MTIP", 1, WARL);
        add_field("UEIP", 1, WARL);
        add_field("SEIP", 1, WARL);
        add_field("WARL2", 1, WARL);
        add_field("MEIP", 1, WARL);
        add_field("WARL3", XLEN-12, WARL);
      end
      // Machine trap-enable register
      MIP: begin
        privil_level = M_LEVEL;
        add_field("USIP",   1,  WARL);
        add_field("SSIP",   1,  WARL);
        add_field("WPRI0",  1,  WPRI);
        add_field("MSIP",   1,  WARL);
        add_field("UTIP",   1,  WARL);
        add_field("STIP",   1,  WARL);
        add_field("WPRI1",  1,  WPRI);
        add_field("MTIP",   1,  WARL);
        add_field("UEIP",   1,  WARL);
        add_field("SEIP",   1,  WARL);
        add_field("WPRI2",  1,  WPRI);
        add_field("MEIP",   1,  WARL);
        add_field("WPRI3",  XLEN - 12,  WPRI);
      end
      // Machine interrupt-enable register
      MIE: begin
        privil_level = M_LEVEL;
        add_field("USIE",   1,  WARL);
        add_field("SSIE",   1,  WARL);
        add_field("WPRI0",  1,  WPRI);
        add_field("MSIE",   1,  WARL);
        add_field("UTIE",   1,  WARL);
        add_field("STIE",   1,  WARL);
        add_field("WPRI1",  1,  WPRI);
        add_field("MTIE",   1,  WARL);
        add_field("UEIE",   1,  WARL);
        add_field("SEIE",   1,  WARL);
        add_field("WPRI2",  1,  WPRI);
        add_field("MEIE",   1,  WARL);
        add_field("WPRI3",  XLEN - 12,  WPRI);
      end
      // Cycle Count Register
      MCYCLE: begin
        privil_level = M_LEVEL;
        add_field("MCYCLE", 64, WPRI);
      end
      // Instruction Count Register
      MINSTRET: begin
        privil_level = M_LEVEL;
        add_field("MINSTRET", 64, WPRI);
      end
      // Cycle Count Register - RV32I only
      MCYCLEH: begin
        privil_level = M_LEVEL;
        add_field("MCYCLEH", 32, WPRI);
      end
      // Instruction Count Register - RV32I only
      MINSTRETH: begin
        privil_level = M_LEVEL;
        add_field("MINSTRETH", 32, WPRI);
      end
      // Hardware Performance Monitor Counters
      [MHPMCOUNTER3:MHPMCOUNTER31]: begin
        privil_level = M_LEVEL;
        add_field($sformatf("%s", reg_name.name()), XLEN, WARL);
      end
      // Hardware Performance Monitor Events
      [MHPMEVENT3:MHPMEVENT31]: begin
        privil_level = M_LEVEL;
        add_field($sformatf("%s", reg_name.name()), XLEN, WARL);
      end
      // Hardware Performance Monitor Counters - RV32I only
      [MHPMCOUNTER3H:MHPMCOUNTER31H]: begin
        if(XLEN != 32) begin
          `uvm_fatal(get_full_name(), $sformatf("Register %s is only in RV32I", reg_name.name()))
        end
        privil_level = M_LEVEL;
        add_field($sformatf("%s", reg_name.name()), 32, WARL);
      end
      // Machine Counter Enable Register
      MCOUNTEREN: begin
        privil_level = M_LEVEL;
        add_field("CY", 1, WARL);
        add_field("TM", 1, WARL);
        add_field("IR", 1, WARL);
        add_field("HPM3", 1, WARL);
        add_field("HPM4", 1, WARL);
        add_field("HPM5", 1, WARL);
        add_field("HPM6", 1, WARL);
        add_field("HPM7", 1, WARL);
        add_field("HPM8", 1, WARL);
        add_field("HPM9", 1, WARL);
        add_field("HPM10", 1, WARL);
        add_field("HPM11", 1, WARL);
        add_field("HPM12", 1, WARL);
        add_field("HPM13", 1, WARL);
        add_field("HPM14", 1, WARL);
        add_field("HPM15", 1, WARL);
        add_field("HPM16", 1, WARL);
        add_field("HPM17", 1, WARL);
        add_field("HPM18", 1, WARL);
        add_field("HPM19", 1, WARL);
        add_field("HPM20", 1, WARL);
        add_field("HPM21", 1, WARL);
        add_field("HPM22", 1, WARL);
        add_field("HPM23", 1, WARL);
        add_field("HPM24", 1, WARL);
        add_field("HPM25", 1, WARL);
        add_field("HPM26", 1, WARL);
        add_field("HPM27", 1, WARL);
        add_field("HPM28", 1, WARL);
        add_field("HPM29", 1, WARL);
        add_field("HPM30", 1, WARL);
        add_field("HPM31", 1, WARL);
        if(XLEN == 64) begin
          add_field("WPRI",  32,  WPRI);
        end
      end
      // Machine Scratch Register
      MSCRATCH: begin
        privil_level = M_LEVEL;
        add_field("MSCRATCH", XLEN, WARL);
      end
      // Machine Exception Program Counter
      MEPC: begin
        privil_level = M_LEVEL;
        add_field("BASE",  XLEN,  WARL);
      end
      // Machine Cause Register
      MCAUSE: begin
        privil_level = M_LEVEL;
        add_field("CODE",  4,  WLRL);
        add_field("WLRL", XLEN-5, WLRL);
        add_field("INTERRUPT",  1,  WARL);
      end
      // Machine Trap Value
      MTVAL: begin
        privil_level = M_LEVEL;
        add_field("VALUE",  XLEN,  WARL);
      end
      // Physical Memory Protection Configuration Register
      PMPCFG0: begin
        privil_level = M_LEVEL;
        add_field("PMP0CFG", 8, WARL);
        add_field("PMP1CFG", 8, WARL);
        add_field("PMP2CFG", 8, WARL);
        add_field("PMP3CFG", 8, WARL);
        if(XLEN==64) begin
          add_field("PMP4CFG", 8, WARL);
          add_field("PMP5CFG", 8, WARL);
          add_field("PMP6CFG", 8, WARL);
          add_field("PMP7CFG", 8, WARL);
        end
      end
      // Physical Memory Protection Configuration Register
      PMPCFG1: begin
        privil_level = M_LEVEL;
        if(XLEN!=32) begin
          `uvm_fatal(`gfn, "CSR PMPCFG1 only exists in RV32.")
        end else begin
          add_field("PMP4CFG", 8, WARL);
          add_field("PMP5CFG", 8, WARL);
          add_field("PMP6CFG", 8, WARL);
          add_field("PMP7CFG", 8, WARL);
        end
      end
      // Physical Memory Protection Configuration Register
      PMPCFG2: begin
        privil_level = M_LEVEL;
        add_field("PMP8CFG", 8, WARL);
        add_field("PMP9CFG", 8, WARL);
        add_field("PMP10CFG", 8, WARL);
        add_field("PMP11CFG", 8, WARL);
        if(XLEN==64) begin
          add_field("PMP12CFG", 8, WARL);
          add_field("PMP13CFG", 8, WARL);
          add_field("PMP14CFG", 8, WARL);
          add_field("PMP15CFG", 8, WARL);
        end
      end
      // Physical Memory Protection Configuration Register
      PMPCFG3: begin
        if(XLEN!=32) begin
          `uvm_fatal(get_full_name(), "CSR PMPCFG3 only exists in RV32.")
        end
        privil_level = M_LEVEL;
        add_field("PMP12CFG", 8, WARL);
        add_field("PMP13CFG", 8, WARL);
        add_field("PMP14CFG", 8, WARL);
        add_field("PMP15CFG", 8, WARL);
      end
      // Physical Memory Protection Configuration Registers
      [PMPADDR0:PMPADDR15]: begin
        privil_level = M_LEVEL;
        if(XLEN==64) begin
          add_field("ADDRESS", 54, WARL);
          add_field("WARL", 10, WARL);
        end else begin
          add_field("ADDRESS", 32, WARL);
        end
      end
      /////////////// Supervisor mode reigster //////////////
      // Supervisor status register
      SSTATUS: begin
        privil_level = S_LEVEL;
        add_field("UIE",   1,  WARL);
        add_field("SIE",   1,  WARL);
        add_field("WPRI0", 2,  WPRI);
        add_field("UPIE",  1,  WARL);
        add_field("SPIE",  1,  WARL);
        add_field("WPRI1", 2,  WPRI);
        add_field("SPP",   1,  WLRL);
        add_field("WPRI2", 4,  WPRI);
        add_field("FS",    2,  WARL);
        add_field("XS",    2,  WARL);
        add_field("WPRI3", 1,  WPRI);
        add_field("SUM",   1,  WARL);
        add_field("MXR",   1,  WARL);
        if(XLEN == 32) begin
          add_field("WPRI4", 11,  WPRI);
        end else begin
          add_field("WPRI4", 12,  WPRI);
          add_field("UXL",   2,  WARL);
          add_field("WPRI4", XLEN - 35, WPRI);
        end
        add_field("SD",   1,  WARL);
      end
      // Supervisor Trap Vector Base Address Register
      STVEC: begin
        privil_level = S_LEVEL;
        add_field("MODE", 2, WARL);
        add_field("BASE", XLEN-2, WLRL);
      end
      // Supervisor Exception Delegation Register
      SEDELEG: begin
        privil_level = S_LEVEL;
        add_field("IAM", 1, WARL);
        add_field("IAF", 1, WARL);
        add_field("II", 1, WARL);
        add_field("WPRI0", 1, WPRI);
        add_field("LAM", 1, WARL);
        add_field("LAF", 1, WARL);
        add_field("SAM", 1, WARL);
        add_field("SAF", 1, WARL);
        add_field("ECFU", 1, WARL);
        add_field("WPRI1", 1, WPRI);
        add_field("WARL0", 1, WARL);
        add_field("WPRI2", 1, WPRI);
        add_field("IPF", 1, WARL);
        add_field("LPF", 1, WARL);
        add_field("WARL1", 1, WARL);
        add_field("SPF", 1, WARL);
        add_field("WARL2", XLEN-16, WARL);
      end
      // Supervisor Interrupt Delegation Register
      SIDELEG: begin
        privil_level = S_LEVEL;
        add_field("USIP", 1, WARL);
        add_field("SSIP", 1, WARL);
        add_field("WARL0", 1, WARL);
        add_field("WPRI0", 1, WPRI);
        add_field("UTIP", 1, WARL);
        add_field("STIP", 1, WARL);
        add_field("WARL1", 1, WARL);
        add_field("WPRI1", 1, WPRI);
        add_field("UEIP", 1, WARL);
        add_field("SEIP", 1, WARL);
        add_field("WARL2", 1, WARL);
        add_field("WPRI2", 1, WPRI);
        add_field("WARL3", XLEN-12, WARL);
      end
      // Supervisor trap-enable register
      SIP: begin
        privil_level = S_LEVEL;
        add_field("USIP",   1,  WARL);
        add_field("SSIP",   1,  WARL);
        add_field("WPRI0",  2,  WPRI);
        add_field("UTIP",   1,  WARL);
        add_field("STIP",   1,  WARL);
        add_field("WPRI1",  2,  WPRI);
        add_field("UEIP",   1,  WARL);
        add_field("SEIP",   1,  WARL);
        add_field("WPRI2", 2, WPRI);
        add_field("WPRI3",  XLEN - 12,  WPRI);
      end
      // Supervisor interrupt-enable register
      SIE: begin
        privil_level = S_LEVEL;
        add_field("USIE",   1,  WARL);
        add_field("SSIE",   1,  WARL);
        add_field("WPRI0",  2,  WPRI);
        add_field("UTIE",   1,  WARL);
        add_field("STIE",   1,  WARL);
        add_field("WPRI1",  2,  WPRI);
        add_field("UEIE",   1,  WARL);
        add_field("SEIE",   1,  WARL);
        add_field("WPRI2",  XLEN - 10,  WPRI);
      end
      // Supervisor Counter Enable Register
      SCOUNTEREN: begin
        privil_level = S_LEVEL;
        add_field("CY", 1, WARL);
        add_field("TM", 1, WARL);
        add_field("IR", 1, WARL);
        add_field("HPM3", 1, WARL);
        add_field("HPM4", 1, WARL);
        add_field("HPM5", 1, WARL);
        add_field("HPM6", 1, WARL);
        add_field("HPM7", 1, WARL);
        add_field("HPM8", 1, WARL);
        add_field("HPM9", 1, WARL);
        add_field("HPM10", 1, WARL);
        add_field("HPM11", 1, WARL);
        add_field("HPM12", 1, WARL);
        add_field("HPM13", 1, WARL);
        add_field("HPM14", 1, WARL);
        add_field("HPM15", 1, WARL);
        add_field("HPM16", 1, WARL);
        add_field("HPM17", 1, WARL);
        add_field("HPM18", 1, WARL);
        add_field("HPM19", 1, WARL);
        add_field("HPM20", 1, WARL);
        add_field("HPM21", 1, WARL);
        add_field("HPM22", 1, WARL);
        add_field("HPM23", 1, WARL);
        add_field("HPM24", 1, WARL);
        add_field("HPM25", 1, WARL);
        add_field("HPM26", 1, WARL);
        add_field("HPM27", 1, WARL);
        add_field("HPM28", 1, WARL);
        add_field("HPM29", 1, WARL);
        add_field("HPM30", 1, WARL);
        add_field("HPM31", 1, WARL);
        if(XLEN == 64) begin
          add_field("WPRI",  32,  WPRI);
        end
      end
      // Supervisor Scratch Register
      SSCRATCH: begin
        privil_level = S_LEVEL;
        add_field("SSCRATCH", XLEN, WARL);
      end
      // Supervisor Exception Program Counter
      SEPC: begin
        privil_level = S_LEVEL;
        add_field("BASE",  XLEN,  WARL);
      end
      // Supervisor Cause Register
      SCAUSE: begin
        privil_level = S_LEVEL;
        add_field("CODE",  4,  WLRL);
        add_field("WLRL", XLEN-5, WLRL);
        add_field("INTERRUPT",  1,  WARL);
      end
      // Supervisor Trap Value
      STVAL: begin
        privil_level = S_LEVEL;
        add_field("VALUE",  XLEN,  WARL);
      end
      // Supervisor Address Translation and Protection
      SATP: begin
        privil_level = S_LEVEL;
        if(XLEN == 32) begin
          add_field("PPN",  22, WARL);
          add_field("ASID", 9,  WARL);
          add_field("MODE", 1,  WARL);
        end else begin
          add_field("PPN",  44, WARL);
          add_field("ASID", 16, WARL);
          add_field("MODE", 4,  WARL);
        end
      end
      /////////////// User mode reigster //////////////
      // User Status Register
      USTATUS: begin
        privil_level = U_LEVEL;
        add_field("UIE", 1, WARL);
        add_field("WPRI0", 3, WPRI);
        add_field("UPIE", 1, WARL);
        add_field("WPRI1", XLEN-5, WPRI);
      end
      // User Trap Vector Base Address Register
      UTVEC: begin
        privil_level = U_LEVEL;
        add_field("MODE", 2, WARL);
        add_field("BASE", XLEN-2, WLRL);
      end
      // User Interrupt-Enable register
      UIE: begin
        privil_level = U_LEVEL;
        add_field("USIE", 1, WARL);
        add_field("WPRI0", 3, WPRI);
        add_field("UTIE", 1, WARL);
        add_field("WPRI1", 3, WPRI);
        add_field("UEIE", 1, WARL);
        add_field("WPRI2", XLEN-9, WPRI);
      end
      // User Trap-Enable register
      UIP: begin
        privil_level = U_LEVEL;
        add_field("USIP", 1, WARL);
        add_field("WPRI0", 3, WPRI);
        add_field("UTIP", 1, WARL);
        add_field("WPRI1", 3, WPRI);
        add_field("UEIP", 1, WARL);
        add_field("WPRI2", XLEN-9, WPRI);
      end
      // User Scratch Register
      USCRATCH: begin
        privil_level = U_LEVEL;
        add_field("MSCRATCH", XLEN, WARL);
      end
      // User Exception Program Counter
      UEPC: begin
        privil_level = U_LEVEL;
        add_field("BASE",  XLEN,  WARL);
      end
      // User Cause Register
      UCAUSE: begin
        privil_level = U_LEVEL;
        add_field("CODE",  4,  WLRL);
        add_field("WLRL", XLEN-5, WLRL);
        add_field("INTERRUPT",  1,  WARL);
      end
      // User Trap Value
      UTVAL: begin
        privil_level = U_LEVEL;
        add_field("VALUE",  XLEN,  WARL);
      end
      default:
        `uvm_fatal(get_full_name(), $sformatf("reg %0s is not supported yet", reg_name.name()))
    endcase
  endfunction

endclass
