// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package i2c_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import i2c_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import i2c_reg_pkg::*;
  import i2c_ral_pkg::*;

  // macro includes
  `include "dv_macros.svh"

  // parameters
  typedef enum int {
    FmtWatermark   = 0,
    RxWatermark    = 1,
    FmtOverflow    = 2,
    RxOverflow     = 3,
    Nak            = 4,
    SclInference   = 5,
    SdaInference   = 6,
    StretchTimeout = 7,
    SdaUnstable    = 8,
    NumI2cIntr     = 9
  } i2c_intr_e;

  typedef enum int {
    None           = 0,
    i2c_ro         = 1,
    i2c_wo         = 2,
    i2c_rw         = 3
  } i2c_request_e;

  // csr and mem total size for IP, TODO confirm below value with spec
  parameter uint I2C_ADDR_MAP_SIZE  = 128;
  // local types
  parameter uint I2C_FMT_FIFO_DEPTH = 32;
  parameter uint I2C_RX_FIFO_DEPTH  = 32;

  // functions
  // get the number of bytes that triggers watermark interrupt
  function automatic int get_watermark_bytes_by_level(int lvl);
    case(lvl)
      0: return 1;
      1: return 4;
      2: return 8;
      3: return 16;
      4: return 30;
      default: begin
        `uvm_fatal("i2c_env_pkg::get_watermark_bytes_by_level",
                   $sformatf("invalid watermark level value - %0d", lvl))
      end
    endcase
  endfunction : get_watermark_bytes_by_level

  // get the number of bytes that triggers break interrupt
  function automatic int get_break_bytes_by_level(int lvl);
    case(lvl)
      0: return 2;
      1: return 4;
      2: return 8;
      3: return 16;
      default: begin
        `uvm_fatal("i2c_env_pkg::get_break_bytes_by_level",
                   $sformatf("invalid break level value - %0d", lvl))
      end
    endcase
  endfunction : get_break_bytes_by_level

  // TX finishes the item at the beginning of last cycle and update reg value
  // in the last 2 cycles, need to avoid driving and checking
  `define TX_IGNORED_PERIOD {1, 2}
  // RX finishes the item at the middle of last cycle and update reg value
  // in the last cycle, need to avoid driving and checking
  `define RX_IGNORED_PERIOD {1}

  // package sources
  `include "i2c_env_cfg.sv"
  `include "i2c_env_cov.sv"
  `include "i2c_virtual_sequencer.sv"
  `include "i2c_scoreboard.sv"
  `include "i2c_env.sv"
  `include "i2c_vseq_list.sv"

endpackage : i2c_env_pkg
