// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package nvm_otp_key_agent_pkg;
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_agent_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Which of the two keys a handshake is for.
  typedef enum bit {
    NvmOtpKeyAddr = 1'b0,
    NvmOtpKeyData = 1'b1
  } nvm_otp_key_kind_e;

  parameter int unsigned NumNvmOtpKeyKinds = 2;

  typedef bit [otp_ctrl_pkg::NvmKeyWidth-1:0] nvm_otp_key_t;

  // Package sources
  `include "nvm_otp_key_item.sv"
  `include "nvm_otp_key_agent_cfg.sv"
  `include "nvm_otp_key_agent_cov.sv"
  `include "nvm_otp_key_monitor.sv"
  `include "nvm_otp_key_sequencer.sv"
  `include "nvm_otp_key_device_driver.sv"
  `include "nvm_otp_key_seq_list.sv"
  `include "nvm_otp_key_agent.sv"
endpackage : nvm_otp_key_agent_pkg
