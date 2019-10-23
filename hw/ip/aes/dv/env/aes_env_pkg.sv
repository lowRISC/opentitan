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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

   parameter uint ADDR_MAP_SIZE      = 2048;
  // types
  // forward declare classes to allow typedefs below
  typedef class aes_env_cfg;
  typedef class aes_env_cov;
//
//  // reuse cip_base_virtual_seqeuencer as is with the right parameter set
 typedef cip_base_virtual_sequencer #(aes_env_cfg, aes_env_cov) aes_virtual_sequencer;

 // typedef class cip_base_virtual_sequencer;


  // functions

  // package sources
 `include "aes_reg_block.sv"
 `include "aes_env_cfg.sv"
 `include "aes_env_cov.sv"
 `include "aes_scoreboard.sv"
 `include "aes_env.sv"
 `include "aes_vseq_list.sv"

endpackage
