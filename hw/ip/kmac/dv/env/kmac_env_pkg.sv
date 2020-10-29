// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package kmac_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import kmac_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types
  typedef enum {
    KmacDone,
    KmacFifoEmpty,
    KmacErr
  } kmac_intr_e;

  // functions

  // package sources
  `include "kmac_env_cfg.sv"
  `include "kmac_env_cov.sv"
  `include "kmac_virtual_sequencer.sv"
  `include "kmac_scoreboard.sv"
  `include "kmac_env.sv"
  `include "kmac_vseq_list.sv"

endpackage
