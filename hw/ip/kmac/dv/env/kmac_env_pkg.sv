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
  import test_vectors_pkg::*;
  import digestpp_dpi_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import push_pull_agent_pkg::*;
  import kmac_ral_pkg::*;
  import keymgr_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // Sideload data has 2*KeyWidth bits of key shares and 1 bit valid.
  parameter int SIDELOAD_KEY_SIZE = $bits(hw_key_req_t);
  // KDF request data has 1 bit for last, and the rest are for data/strb.
  // We subtract 1 from the width of the struct as it includes the valid handshake signal.
  parameter int KDF_DATA_SIZE = $bits(kmac_data_req_t) - 1;
  // KDF response data has 2 bits for done/error signals and the rest are for digest shares.
  // We subtract 1 from the struct width as it includes the ready handshake signal.
  parameter int KDF_DIGEST_SIZE = $bits(kmac_data_rsp_t) - 1;

  // types
  typedef enum {
    KmacDone,
    KmacFifoEmpty,
    KmacErr
  } kmac_intr_e;

  typedef virtual pins_if#(1)       idle_vif;
  typedef virtual kmac_sideload_if  sideload_vif;

  // functions

  // package sources
  `include "kmac_env_cfg.sv"
  `include "kmac_env_cov.sv"
  `include "kmac_virtual_sequencer.sv"
  `include "kmac_scoreboard.sv"
  `include "kmac_env.sv"
  `include "kmac_vseq_list.sv"

endpackage
