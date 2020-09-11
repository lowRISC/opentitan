// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package keymgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import keymgr_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // TODO update below, or compile error occurs
  parameter uint KEYMGR_ADDR_MAP_SIZE = 256;

  // types

  // functions

  // package sources
  `include "keymgr_env_cfg.sv"
  `include "keymgr_env_cov.sv"
  `include "keymgr_virtual_sequencer.sv"
  `include "keymgr_scoreboard.sv"
  `include "keymgr_env.sv"
  `include "keymgr_vseq_list.sv"

endpackage
