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
    FmtWatermark = 0,
    RxWatermark = 1,
    FmtOverflow = 2,
    RxOverflow = 3,
    Nak = 4,
    SclInference = 5,
    SdaInference = 6,
    StretchTimeout = 7,
    SdaUnstable = 8,
    TransComplete = 9,
    NumI2cIntr = 10
  } i2c_intr_e;

  typedef enum int {
    ReadOnly = 0,
    WriteOnly = 1,
    ReadWrite = 2
  } tran_type_e;

  // csr and mem total size for IP, TODO confirm below value with spec
  parameter uint I2C_ADDR_MAP_SIZE = 128;
  parameter uint I2C_FMT_FIFO_DEPTH = 32;
  parameter uint I2C_RX_FIFO_DEPTH = 32;

  // for constrains
  parameter uint I2C_MIN_TRAN = 30;
  parameter uint I2C_MAX_TRAN = 50;
  parameter uint I2C_MIN_ADDR = 0;
  parameter uint I2C_MAX_ADDR = 127;
  parameter uint I2C_MIN_DLY = 0;
  parameter uint I2C_MAX_DLY = 5;
  parameter uint I2C_MIN_DATA = 0;
  parameter uint I2C_MAX_DATA = 255;
  parameter uint I2C_MIN_TIMING = 1;  // at least 1
  parameter uint I2C_MAX_TIMING = 5;
  parameter uint I2C_TIME_RANGE = I2C_MAX_TIMING - I2C_MIN_TIMING;
  parameter uint I2C_MIN_TIMEOUT = 1;
  parameter uint I2C_MAX_TIMEOUT = 4;
  parameter uint I2C_MAX_RXILVL = 7;
  parameter uint I2C_MAX_FMTILVL = 3;
  parameter uint I2C_IDLE_TIME = 5000;
  // package sources
  `include "i2c_env_cfg.sv"
  `include "i2c_env_cov.sv"
  `include "i2c_virtual_sequencer.sv"
  `include "i2c_scoreboard.sv"
  `include "i2c_env.sv"
  `include "i2c_vseq_list.sv"

endpackage : i2c_env_pkg

