// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// target specific signals inside the CTR mode FSM
interface fi_ctr_fsm_if
  import uvm_pkg::*;
  import aes_pkg::*;
  (
   input logic      clk_i,
   input logic      rst_ni,
   input aes_ctr_e  aes_ctr_cs
  );

  `include "dv_fcov_macros.svh"
  // get bind path to module
  string       par_hier = dv_utils_pkg::get_parent_hier($sformatf("%m"), 2);

  // single bit forces
  string intf_array[] = {
    $sformatf("%s.%s", par_hier, "incr_i"),
    $sformatf("%s.%s", par_hier, "ready_o"),
    $sformatf("%s.%s", par_hier, "ctr_we_o")
   };


  function automatic int get_if_size();
    return intf_array.size();
  endfunction // get_if_size

  // check which array we need to access and force or releae
  function automatic void force_signal(int target, bit rel, bit [31:0] value);
    if (!rel) aes_ctr_fsm_cg_inst.sample(target);
    if (!rel) force_single_bit(target);
    else release_single_bit(target);
  endfunction // force_signal


  function automatic void force_single_bit(int target);

    //VCS coverage off
    // pragma coverage off

    bit  read;
    $assertoff(0, "tb.dut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscDataOut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscIv");
    if (!uvm_hdl_check_path(intf_array[target])) begin
      `uvm_fatal("fi_ctr_fsm_if", $sformatf("PATH NOT EXISTING %m"))
    end
    // read the value currently
    if (!uvm_hdl_read(intf_array[target], read)) begin
      `uvm_error("fi_ctr_fsm_if", $sformatf("Was not able to read %s", intf_array[target]))
    end
    // always announce we are forcing something
    `uvm_info("if_ctr_fsm_if",
       $sformatf(" I am forcing target %d %s, value %b",target, intf_array[target], !read),UVM_LOW);
    if (!uvm_hdl_force(intf_array[target],!read)) begin
      `uvm_error("fi_ctr_fsm_if", $sformatf("Was not able to force %s", intf_array[target]))
    end

    //VCS coverage on
    // pragma coverage on

  endfunction


  function automatic void release_single_bit(int target);

    //VCS coverage off
    // pragma coverage off

    if (!uvm_hdl_release(intf_array[target])) begin
      `uvm_error("fi_ctr_fsm_if", $sformatf("Was not able to release %s", intf_array[target]))
    end

    //VCS coverage on
    // pragma coverage on

    $asserton(0,"tb.dut");
  endfunction


  ///////////////////////////////////
  // Fault inject coverage         //
  ///////////////////////////////////

  covergroup aes_ctr_fsm_cg (int num_bins) with function sample(int target);
    // We want to see coverage per instance,
    // but as the code are copies of eachother
    // we don't need every instance to achieve 100% coverage
    // a total of 100% is enough so we set the option
    // to merge the coverage of the instances
    option.per_instance         = 0;
    option.name                 = "aes_ctr_fsm_interleave_cg";
    type_option.merge_instances = 1;

    cp_target: coverpoint target
      {
         bins signal_target[] = {[0:num_bins-1]};
      }

    // A fault is injected in each state.  Ignore the error state because it is the result of
    // a fault and not a regular operating condition in which faults are expected to be handled.
    cp_state: coverpoint aes_ctr_cs {
      ignore_bins error = {aes_pkg::CTR_ERROR};
    }

    // Each target signal is faulted in each state.
    target_state_cross: cross cp_target, cp_state;
  endgroup

  //aes_ctr_fsm_cg my_cg = new(intf_array.size() + intf_mul_array.size() -1);
  `DV_FCOV_INSTANTIATE_CG(aes_ctr_fsm_cg, 1'b1, (intf_array.size()) )
endinterface
