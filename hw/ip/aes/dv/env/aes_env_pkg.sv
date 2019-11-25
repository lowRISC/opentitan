// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import aes_reg_pkg::*;
  import aes_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

   parameter uint AES_ADDR_MAP_SIZE      = 128;
  // types
  // forward declare classes to allow typedefs below
  typedef class aes_env_cfg;
  typedef class aes_env_cov;

  // functions

  // package sources
 `include "aes_env_cfg.sv"
 `include "aes_seq_item.sv"
 `include "aes_env_cov.sv"
 `include "aes_virtual_sequencer.sv"
 `include "aes_scoreboard.sv"
 `include "aes_env.sv"
 `include "aes_vseq_list.sv"

endpackage
