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

  // Sources.
  `include "sba_access_item.sv"
  `include "sba_access_monitor.sv"
  `include "sba_access_reg_frontdoor.sv"
  `include "jtag_rv_debugger.sv"

endpackage
