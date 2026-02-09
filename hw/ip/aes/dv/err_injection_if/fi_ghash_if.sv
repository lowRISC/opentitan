// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// target specific signals inside aes_ghash.sv
interface fi_ghash_if
  import uvm_pkg::*;
  import aes_pkg::*;
  (
   input logic       clk_i,
   input logic       rst_ni,
   input aes_ghash_e aes_ghash_cs
   );

  `include "dv_fcov_macros.svh"
  // get bind path to module
  string       par_hier = dv_utils_pkg::get_parent_hier($sformatf("%m"), 2);

  // multi bit forces
  string intf_mul_array[] = {
    // signals triggering fatal alerts locally
    $sformatf("%s.%s", par_hier, "aes_ghash_cs"),
    $sformatf("%s.%s", par_hier, "ghash_add_in_sel_q[0]"),
    $sformatf("%s.%s", par_hier, "ghash_add_in_sel_q[1]"),
    $sformatf("%s.%s", par_hier, "gf_mult1_in_sel_q"),
    $sformatf("%s.%s", par_hier, "gcm_phase_i"),
    // signals triggering fatal alerts elsewhere
    $sformatf("%s.%s", par_hier, "in_ready_o"),
    $sformatf("%s.%s", par_hier, "out_valid_o")
  };

  // check whether the given hier_name ends with signal_name
  function automatic int check_target_name(string hier_name, string signal_name);
    int hier_len = hier_name.len();
    int signal_len = signal_name.len();
    if (str_utils_pkg::str_rfind(hier_name, signal_name,
                                 hier_len - signal_len - 1, -1) == -1) begin
      return 0;
    end else begin
      return 1;
    end
  endfunction

  function automatic int get_if_size();
    return intf_mul_array.size();
  endfunction // get_if_size

  // check which array we need to access and force or releae
  function automatic void force_signal(int target, bit rel, bit [31:0] value);
    if (!rel) begin
      aes_ghash_cg_inst.sample(target);
      force_multi_bit((target), value);
    end else begin
      release_multi_bit(target);
    end
  endfunction // force_signal

  function automatic void force_multi_bit(int target, bit [31:0] value);

    //VCS coverage off
    // pragma coverage off

    bit [31:0] read;
    bit [31:0] mask = '0;
    $assertoff(0, "tb.dut");
    $asserton(1, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscDataOut");
    $asserton(1, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscIv");

    // Some signals only exist for the masked implementation. Skip those when testing the unmasked
    // implementation.
    if (`EN_MASKING == 0) begin
      if (check_target_name(intf_mul_array[target], "ghash_add_in_sel_q[0]") ||
          check_target_name(intf_mul_array[target], "ghash_add_in_sel_q[1]") ||
          check_target_name(intf_mul_array[target], "gf_mult1_in_sel_q")) begin
        target = $urandom_range(4, get_if_size()-1);
      end
    end

    if (!uvm_hdl_check_path(intf_mul_array[target])) begin
      `uvm_fatal("fi_ghash_if", $sformatf("PATH NOT EXISTING %m"))
    end
    // Read the current value.
    if (!uvm_hdl_read(intf_mul_array[target], read)) begin
      `uvm_error("fi_ghash_if", $sformatf("Was not able to read %s", intf_mul_array[target]))
    end

    if (check_target_name(intf_mul_array[target], "aes_ghash_cs")) begin
      // For the GHASH FSM state, we have to force an invalid value to trigger an alert.
      while (value[aes_pkg::GhashStateWidth-1:0] inside {GHASH_IDLE,
                                                         GHASH_MULT,
                                                         GHASH_ADD_S,
                                                         GHASH_OUT,
                                                         GHASH_MASKED_INIT,
                                                         GHASH_MASKED_ADD_STATE_SHARES,
                                                         GHASH_MASKED_ADD_CORR,
                                                         GHASH_MASKED_SETTLE}) begin
        value = $urandom();
      end
    end else if (check_target_name(intf_mul_array[target], "ghash_add_in_sel_q[0]") ||
                 check_target_name(intf_mul_array[target], "ghash_add_in_sel_q[1]") ||
                 check_target_name(intf_mul_array[target], "gf_mult1_in_sel_q")     ||
                 check_target_name(intf_mul_array[target], "gcm_phase_i")) begin
      // These signals must be zero or one-hot. Make sure to set at least two bits.
      while ($countones(mask[2:0]) < 2) begin
        mask = $urandom();
      end
      value = read | mask;
    end else if (check_target_name(intf_mul_array[target], "in_ready_o") ||
                 check_target_name(intf_mul_array[target], "out_valid_o")) begin
      // These signals are sp2v_e and can detect up to two flipped bits.
      while ($countones(mask[2:0]) < 1 || $countones(mask[2:0]) > 2) begin
        mask = $urandom();
      end
      value = read ^ mask;
    end
    `uvm_info("if_ghash_if",
        $sformatf(" I am forcing target %0d %s, value %b", target, intf_mul_array[target], value),
        UVM_LOW);
    if (!uvm_hdl_force(intf_mul_array[target], value)) begin
      `uvm_error("fi_ghash_if", $sformatf("Was not able to force %s", intf_mul_array[target]))
    end

    //VCS coverage on
    // pragma coverage on

  endfunction

  function automatic void release_multi_bit(int target);

    //VCS coverage off
    // pragma coverage off

    if (!uvm_hdl_release(intf_mul_array[target])) begin
      `uvm_error("fi_ghash_if", $sformatf("Was not able to release %s", intf_mul_array[target]))
    end

    //VCS coverage on
    // pragma coverage on

    $asserton(0,"tb.dut");
  endfunction

  ///////////////////////////////////
  // Fault inject coverage         //
  ///////////////////////////////////

  covergroup aes_ghash_cg (int num_bins) with function sample(int target);
    option.per_instance = 1;
    option.name         = "aes_ghash_interleave_cg";

    cp_target: coverpoint target
      {
         bins signal_target[] = {[0:num_bins-1]};
      }

    // A fault is injected in each state.  Ignore the error state because it is the result of
    // a fault and not a regular operating condition in which faults are expected to be handled.
    cp_state: coverpoint aes_ghash_cs {
      ignore_bins error = {aes_pkg::GHASH_ERROR};
    }

    // Each target signal is faulted in each state.
    target_state_cross: cross cp_target, cp_state;
  endgroup // aes_ghash_cg

  `DV_FCOV_INSTANTIATE_CG(aes_ghash_cg, 1'b1, (intf_mul_array.size()) )

  function automatic void cg_aes_ghash_sample(int target);
    aes_ghash_cg_inst.sample(target);
  endfunction // cg_aes_ghash_sample

endinterface
