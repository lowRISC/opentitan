// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package jtag_riscv_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import jtag_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // JTAG TAP for DMI according to debug spec 0.13
  parameter uint DMI_OPW   = 2;
  parameter uint DMI_DATAW = 32;
  parameter uint DMI_ADDRW = 7;
  parameter uint DMI_IRW   = 5;
  parameter uint DMI_DRW   = DMI_OPW + DMI_DATAW + DMI_ADDRW;
  parameter uint DTMCS_DRW = 32;

  // local types
  typedef enum bit [DMI_IRW-1:0] {
    JtagBypass0   = 'h0,
    JtagIdcode    = 'h1,
    JtagDtmCsr    = 'h10,
    JtagDmiAccess = 'h11,
    JtagBypass1   = 'h1f
  } jtag_ir_e;

  typedef enum bit [DMI_OPW-1:0] {
    DmiNoErr      = 'h0,
    DmiFail       = 'h2,
    DmiInProgress = 'h3
  } jtag_op_status_e;

  typedef enum bit [DMI_OPW-1:0] {
    DmiStatus = 'h0,
    DmiRead   = 'h1,
    DmiWrite  = 'h2
  } jtag_op_e;

  typedef enum bit [4:0] {
    DmiReset     = 16,
    DmiHardReset = 17
  } jtag_dtmcs_e;

  // forward declare classes to allow typedefs below
  typedef class jtag_riscv_item;
  typedef class jtag_riscv_agent_cfg;

  // this dummy driver is defined to avoid compile errors in dv_base_agent.
  typedef dv_base_driver #(jtag_riscv_item, jtag_riscv_agent_cfg) jtag_riscv_driver;

  // package sources
  `include "jtag_riscv_item.sv"
  `include "jtag_riscv_agent_cfg.sv"
  `include "jtag_riscv_agent_cov.sv"
  `include "jtag_riscv_monitor.sv"
  `include "jtag_riscv_sequencer.sv"
  `include "jtag_riscv_agent.sv"
  `include "jtag_riscv_seq_list.sv"

endpackage: jtag_riscv_agent_pkg
