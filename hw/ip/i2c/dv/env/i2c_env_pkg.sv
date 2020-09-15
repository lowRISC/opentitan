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
    TransComplete  = 9,
    TxEmpty        = 10,
    TxNonEmpty     = 11,
    TxOverflow     = 12,
    AcqOverflow    = 13,
    AckStop        = 14,
    NumI2cIntr     = 15
  } i2c_intr_e;

  typedef enum int {
    ReadOnly  = 0,
    WriteOnly = 1,
    ReadWrite = 2
  } tran_type_e;

  parameter uint I2C_FMT_FIFO_DEPTH = 32;
  parameter uint I2C_RX_FIFO_DEPTH  = 32;

  // package sources
  `include "i2c_seq_cfg.sv"
  `include "i2c_env_cfg.sv"
  `include "i2c_env_cov.sv"
  `include "i2c_virtual_sequencer.sv"
  `include "i2c_scoreboard.sv"
  `include "i2c_env.sv"
  `include "i2c_vseq_list.sv"

endpackage : i2c_env_pkg

