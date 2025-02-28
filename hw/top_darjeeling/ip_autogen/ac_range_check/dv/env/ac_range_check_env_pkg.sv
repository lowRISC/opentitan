// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ac_range_check_env_pkg;
  // Dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import ac_range_check_ral_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Imports from packages
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_bool_to_mubi;
  import prim_mubi_pkg::mubi4_logic_test_true_strict;
  import prim_mubi_pkg::mubi8_t;
  import prim_mubi_pkg::MuBi8False;

  // Parameters
  parameter uint   NUM_ALERTS       = 2;
  parameter string LIST_OF_ALERTS[] = {"recov_ctrl_update_err", "fatal_fault"};
  parameter uint   NUM_RANGES       = 32;

  // Types
  typedef enum int {
    DenyCntReached = 0
  } ac_range_check_intr_e;

  typedef struct packed {
    bit log_denied_access;
    bit execute_access;
    bit write_access;
    bit read_access;
    bit enable;
  } range_perm_t;

  typedef struct packed {
    bit [15:0] write_perm;
    bit [15:0] read_perm;
  } racl_policy_t;

  typedef struct packed {
    bit                 rand_write;
    bit                 write;
    bit                 rand_addr;
    bit [AddrWidth-1:0] addr;
    bit                 rand_mask;
    bit [MaskWidth-1:0] mask;
    bit                 rand_data;
    bit [DataWidth-1:0] data;
  } tl_main_vars_t;

  typedef enum bit [1:0] {
    AddrRead  = 0,
    AddrWrite = 1,
    DataRead  = 2,
    DataWrite = 3
  } tl_phase_e;

  // Functions
  // Retrieve the index of the CSR based on its name
  function automatic int get_csr_idx(string csr_ral_name, string csr_name);
    string csr_name_with_idx;
    for (int idx=0; idx<NUM_RANGES; idx++) begin
      csr_name_with_idx = $sformatf("%0s_%0d", csr_name, idx);
      if (csr_name_with_idx == csr_ral_name) begin
        return idx;
      end
    end
    return -1;
  endfunction : get_csr_idx

  // Package sources
  `include "ac_range_check_dut_cfg.sv"
  `include "ac_range_check_env_cfg.sv"
  `include "ac_range_check_env_cov.sv"
  `include "ac_range_check_virtual_sequencer.sv"
  `include "ac_range_check_scoreboard.sv"
  `include "ac_range_check_env.sv"
  `include "ac_range_check_vseq_list.sv"
endpackage : ac_range_check_env_pkg
