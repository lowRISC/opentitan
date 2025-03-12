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
    $sformatf("%s.%s", par_hier, "aes_ghash_cs")
  };

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

    $assertoff(0, "tb.dut");
    $asserton(1, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscDataOut");
    $asserton(1, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscIv");
    if (!uvm_hdl_check_path(intf_mul_array[target])) begin
      `uvm_fatal("fi_ghash_if", $sformatf("PATH NOT EXISTING %m"))
    end
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
