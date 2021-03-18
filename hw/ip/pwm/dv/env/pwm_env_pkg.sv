// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwm_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import pwm_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import pwm_reg_pkg::*;
  import pwm_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types

  // functions

  // package sources
  `include "pwm_seq_cfg.sv"
  `include "pwm_env_cfg.sv"
  `include "pwm_env_cov.sv"
  `include "pwm_virtual_sequencer.sv"
  `include "pwm_scoreboard.sv"
  `include "pwm_env.sv"
  `include "pwm_vseq_list.sv"

endpackage
