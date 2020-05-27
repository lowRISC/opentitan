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

  // csr and mem total size for IP, TODO confirm below value with spec
  parameter uint I2C_ADDR_MAP_SIZE = 128;

  // for constrains
  parameter uint I2C_MIN_TRAN    = 10;
  parameter uint I2C_MAX_TRAN    = 200;
  parameter uint I2C_MIN_ADDR    = 0;
  parameter uint I2C_MAX_ADDR    = 127;
  parameter uint I2C_MIN_DLY     = 0;
  parameter uint I2C_MAX_DLY     = 2;
  parameter uint I2C_MIN_DATA    = 0;
  parameter uint I2C_MAX_DATA    = 255;
  parameter uint I2C_MIN_TIMING  = 1;     // at least 1
  parameter uint I2C_MAX_TIMING  = 5;
  parameter uint I2C_TIME_RANGE  = I2C_MAX_TIMING - I2C_MIN_TIMING;
  parameter uint I2C_TIMEOUT_ENB = 1;
  parameter uint I2C_MIN_TIMEOUT = 1;
  parameter uint I2C_MAX_TIMEOUT = 2;
  parameter uint I2C_IDLE_TIME   = 1200;

  // ok_to_end_delay_ns for EoT
  parameter uint DELAY_FOR_EOT_NS = 5000;

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

  // package sources
  `include "i2c_env_cfg.sv"
  `include "i2c_env_cov.sv"
  `include "i2c_virtual_sequencer.sv"
  `include "i2c_scoreboard.sv"
  `include "i2c_env.sv"
  `include "i2c_vseq_list.sv"

endpackage : i2c_env_pkg

