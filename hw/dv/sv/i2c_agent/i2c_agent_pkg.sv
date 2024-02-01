// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I2C specification (revision 6):
// https://web.archive.org/web/20210813122132/https://www.nxp.com/docs/en/user-guide/UM10204.pdf

package i2c_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Bus/Transaction types for the agent driver
  typedef enum logic [3:0] {
    None, DevAck, DevNack, RdData, WrData,
    HostStart, HostRStart, HostData, HostAck,
    HostNAck, HostStop, HostDataNoWaitForACK,
    HostWait
  } drv_type_e;

  // Driver phase
  typedef enum int {
    DrvIdle,
    DrvStart,
    DrvAddr,
    DrvWr,
    DrvRd,
    DrvStop
  } drv_phase_e;

  // register values
  typedef struct {
    // derived parameters
    bit  [31:0]  tSetupStart;
    bit  [31:0]  tHoldStart;
    bit  [31:0]  tClockStart;
    bit  [31:0]  tClockLow;
    bit  [31:0]  tSetupBit;
    bit  [31:0]  tClockPulse;
    bit  [31:0]  tHoldBit;
    bit  [31:0]  tClockStop;
    bit  [31:0]  tSetupStop;
    bit  [31:0]  tHoldStop;
    bit          enbTimeOut;
    bit  [30:0]  tTimeOut;
    uint         tStretchHostClock;

    // sda_unstable interrupt will be asserted if
    // tSdaUnstable is set to a non-zero value, otherwise
    uint         tSdaUnstable;
    // scl_interference interrupt will be asserted if
    // tSclInterference is set to a zero value, otherwise
    uint         tSclInterference;
    // sda_interference interrupt will be asserted if
    // tSdaInterference is set to a zero value, otherwise
    uint         tSdaInterference;
  } timing_cfg_t;

  typedef enum int {
    Addr7BitMode  = 7,
    Addr10BitMode = 10
  } i2c_target_addr_mode_e;

  // forward declare classes to allow typedefs below
  typedef class i2c_item;
  typedef class i2c_agent_cfg;

  // package sources
  `include "i2c_item.sv"
  `include "i2c_agent_cfg.sv"
  `include "i2c_agent_cov.sv"
  `include "i2c_monitor.sv"
  `include "i2c_driver.sv"
  `include "i2c_sequencer.sv"
  `include "i2c_agent.sv"
  `include "seq_lib/i2c_seq_list.sv"

endpackage: i2c_agent_pkg
