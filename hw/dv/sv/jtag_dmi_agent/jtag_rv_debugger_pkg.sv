// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A package that models a RISC-V JTAG debugger.
//
// These utilities are semi-compliant with RISCV debug specification 0.13.2:
// https://github.com/riscv/riscv-debug-spec/raw/4e0bb0fc2d843473db2356623792c6b7603b94d4/
// riscv-debug-release.pdf
//
// OpenTitan uses the implementation of this spec in the PULP debug repository located at:
// https://github.com/pulp-platform/riscv-dbg
//
// This is built on top of the capabilities provided by the jtag_dmi_agent_pkg.
//
// To access the chip resources over the SBA interface, it provides an SBA request item type as a
// class, in sba_access_item. It also provides an sba_access_monitor, which generates predicted SBA
// traffic based on SBA accesses sent.
package jtag_rv_debugger_pkg;
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import bus_params_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import dv_lib_pkg::*;
  import jtag_agent_pkg::*;
  import jtag_dmi_agent_pkg::*;

  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Abstract command types.
  typedef enum logic [7:0] {
    AbstractCmdRegAccess = 0,
    AbstractCmdQuickAccess = 1,
    AbstractCmdMemAccess = 2
  } abstract_cmd_type_e;

  // The register number.
  typedef logic [15:0] abstract_cmd_regno_t;

  // Abstract command register access struct.
  typedef struct packed {
    logic                 zero1;
    logic [2:0]           aarsize;
    logic                 aarpostincrement;
    logic                 postexec;
    logic                 transfer;
    logic                 write;
    abstract_cmd_regno_t  regno;
  } abstract_cmd_reg_access_t;

  // The abstract command error types.
  typedef enum logic [2:0] {
    AbstractCmdErrNone,
    AbstractCmdErrBusy,
    AbstractCmdErrUnsupported,
    AbstractCmdErrException,
    AbstractCmdErrHartUnavailable,
    AbstractCmdErrBusError,
    AbstractCmdErrReserved,
    AbstractCmdErrOther
  } abstract_cmd_err_e;

  // SBA access size.
  typedef enum logic [2:0] {
    SbaAccessSize8b,
    SbaAccessSize16b,
    SbaAccessSize32b,
    SbaAccessSize64b,
    SbaAccessSize128b
  } sba_access_size_e;

  // SBA access error types.
  typedef enum logic [2:0] {
    SbaErrNone = 0,
    SbaErrTimeout = 1,
    SbaErrBadAddr = 2,
    SbaErrBadAlignment = 3,
    SbaErrBadSize = 4,
    SbaErrOther = 7
  } sba_access_err_e;

  // The standard RISCV registers.
  //
  // Only some are captured here. More can be added if the need arises.
  // See: https://riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf (section 4.8) for
  // more details.
  typedef enum abstract_cmd_regno_t {
    // Debug CSRs.
    RvCoreCsrDcsr = 'h7b0,
    RvCoreCsrDpc = 'h7b1,
    RvCoreCsrDScratch0 = 'h7b2,
    RvCoreCsrDScratch1 = 'h7b3,

    // Trigger CSRs.
    RvCoreCsrTSelect = 'h7a0,
    RvCoreCsrTData1 = 'h7a1,
    RvCoreCsrTData2 = 'h7a2,
    RvCoreCsrTData3 = 'h7a3,
    RvCoreCsrTInfo = 'h7a4,
    RvCoreCsrMContext = 'h7a8,
    RvCoreCsrSContext = 'h7aa,

    // GPRs ABI Name (these map to x0-x31) (based on RV ISA).
    RvCoreCsrGprZero = 'h1000,
    RvCoreCsrGprRa,
    RvCoreCsrGprSp,
    RvCoreCsrGprGp,
    RvCoreCsrGprTp,
    RvCoreCsrGprT[0:2],
    RvCoreCsrGprS[0:1],
    RvCoreCsrGprA[0:7],
    RvCoreCsrGprS[2:11],
    RvCoreCsrGprT[3:6]
  } rv_core_csr_e;

  // CPU privilege levels
  typedef enum logic [1:0] {
    RvPrivilegeLevelM = 2'b11,
    RvPrivilegeLevelS = 2'b01,
    RvPrivilegeLevelU = 2'b00
  } rv_privilege_level_e;

  // Debug mode causes.
  typedef enum logic [2:0] {
    RvDebugCauseNone = 0,
    RvDebugCauseEbreak = 1,
    RvDebugCauseTrigger = 2,
    RvDebugCauseHaltReq = 3,
    RvDebugCauseStep = 4,
    RvDebugCauseResetHaltReq = 5
  } rv_core_csr_dcsr_cause_e;

  // Ways to access the system memory.
  typedef enum logic [1:0] {
    MemAccessViaAbstractCmd,  // Unsupported.
    MemAccessViaProgbuf,
    MemAccessViaSba
  } mem_access_route_e;

  // Typical commands used in debugger activities.
  typedef enum logic [31:0] {
    Illegal = 'h0,
    Fence = 'hf,
    Nop = 'h13,
    AddiS0S04 = 'h440413, // addr s0, s0, 4
    SwS1S0 = 'h942023,  // swr s1 0(s0)
    LwS0S0 = 'h42403,  // lw s0, 0(s0)
    LwS1S0 = 'h42483,  // lw s1, 0(s0)
    FenceI = 'h100f,
    Ebreak = 'h100073,
    Wfi = 'h10500073
  } rv_opcode_e;

  // DCSR fields.
  //
  // See: https://riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf (section 4.8.1) for
  // more details.
  typedef struct packed {
    logic [3:0]               xdebugver;
    logic [11:0]              zero2;
    logic                     ebreakm;
    logic                     zero1;
    logic                     ebreaks;
    logic                     ebreaku;
    logic                     stepie;
    logic                     stopcount;
    logic                     stoptime;
    rv_core_csr_dcsr_cause_e  cause;
    logic                     zero0;
    logic                     mprven;
    logic                     nmip;
    logic                     step;
    rv_privilege_level_e      prv;
  } rv_core_csr_dcsr_t;

  // Types of triggers.
  typedef enum logic [3:0] {
    RvTriggerTypeNone = 0,
    RvTriggerTypeLegacy = 1,
    RvTriggerTypeMatch = 2,
    RvTriggerTypeICount = 3,
    RvTriggerTypeException = 4
  } rv_core_csr_trigger_type_e;

  typedef enum logic [3:0] {
    RvTriggerActionRaiseBreakpointException = 0,
    RvTriggerActionEnterDebugMode = 1,
    RvTriggerActionReserved[2:15]
  } rv_core_csr_trigger_action_e;

  // Address / data match trigger control CSR.
  typedef struct packed {
    rv_core_csr_trigger_type_e    trigger_type;  // 31:28
    logic                         dmode;
    logic [5:0]                   maskmax;
    logic                         hit;  // 20
    logic                         select;
    logic                         timing;
    logic [1:0]                   sizelo;
    rv_core_csr_trigger_action_e  action;
    logic                         chain;  // 12
    logic [3:0]                   match;
    logic                         m;
    logic                         zero;
    logic                         s;
    logic                         u;
    logic                         execute;
    logic                         store;
    logic                         load;
  } rv_core_csr_trigger_mcontrol_t;

  // A generic breakpoint datastructure.
  typedef struct packed {
    rv_core_csr_trigger_type_e  trigger_type;
    int unsigned                index;
    logic [BUS_DW-1:0]          tdata1;
    logic [BUS_DW-1:0]          tdata2;
  } breakpoint_t;

  // Sources.
  `include "sba_access_item.sv"
  `include "sba_access_monitor.sv"
  `include "sba_access_reg_frontdoor.sv"
  `include "jtag_rv_debugger.sv"

endpackage
