// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// target specific signals inside the main control FSM
interface fi_control_if
  import uvm_pkg::*;
  import aes_pkg::*;
  (
   input logic      clk_i,
   input logic      rst_ni,
   input aes_ctrl_e aes_ctrl_cs
   );

  `include "dv_fcov_macros.svh"
  // get bind path to module
  string       par_hier = dv_utils_pkg::get_parent_hier($sformatf("%m"), 2);

  // single bit forces
  string intf_array[] = {
    $sformatf("%s.%s", par_hier, "data_out_we_o"),
    $sformatf("%s.%s", par_hier, "data_in_prev_we_o"),
    $sformatf("%s.%s", par_hier, "ctr_incr_o"),
    $sformatf("%s.%s", par_hier, "ctr_ready_i"),
    $sformatf("%s.%s", par_hier, "cipher_in_valid_o"),
    $sformatf("%s.%s", par_hier, "cipher_in_ready_i"),
    $sformatf("%s.%s", par_hier, "cipher_out_valid_i"),
    $sformatf("%s.%s", par_hier, "cipher_out_ready_o"),
    $sformatf("%s.%s", par_hier, "cipher_crypt_o"),
    $sformatf("%s.%s", par_hier, "cipher_crypt_i"),
    $sformatf("%s.%s", par_hier, "cipher_dec_key_gen_o"),
    $sformatf("%s.%s", par_hier, "cipher_dec_key_gen_i")
  };

  // multi bit forces
  string intf_mul_array[] = {
    $sformatf("%s.%s", par_hier, "ctr_we_i"),
    $sformatf("%s.%s", par_hier, "key_init_we_o"),
    $sformatf("%s.%s", par_hier, "iv_we_o"),
    $sformatf("%s.%s", par_hier, "data_in_prev_sel_o"),
    $sformatf("%s.%s", par_hier, "state_in_sel_o"),
    $sformatf("%s.%s", par_hier, "add_state_in_sel_o"),
    $sformatf("%s.%s", par_hier, "add_state_out_sel_o"),
    $sformatf("%s.%s", par_hier, "key_init_sel_o"),
    $sformatf("%s.%s", par_hier, "iv_sel_o")
  };

  function automatic int get_if_size();
    return intf_array.size() + intf_mul_array.size();
  endfunction // get_if_size

  // check which array we need to access and force or releae
  function automatic void force_signal(int target, bit rel, bit [31:0] value);
    if (!rel) aes_ctrl_fsm_cg_inst.sample(target);
    if (target < intf_array.size()) begin
      if (!rel) force_single_bit(target);
      else release_single_bit(target);
    end else begin
      if (!rel) force_multi_bit((target - intf_array.size()), value);
      else release_multi_bit(target-intf_array.size());
    end
  endfunction // force_signal


  function automatic void force_single_bit(int target);
    bit  read;
    $assertoff(0, "tb.dut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscDataOut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscIv");
    if (!uvm_hdl_check_path(intf_array[target])) begin
      `uvm_fatal("fi_control_if", $sformatf("PATH NOT EXISTING %m"))
    end
    // read the value currently
    uvm_hdl_read(intf_array[target], read);
    // always announce we are forcing something
    `uvm_info("if_control_if",
       $sformatf(" I am forcing target %d %s, value %b",target, intf_array[target], !read),UVM_LOW);
    if (!uvm_hdl_force(intf_array[target],!read)) begin
      `uvm_error("fi_control_if", $sformatf("Was not able to force %s", intf_array[target]))
    end
  endfunction


  function automatic void release_single_bit(int target);
    uvm_hdl_release(intf_array[target]);
    $asserton(0,"tb.dut");
  endfunction


  function automatic void force_multi_bit(int target, bit [31:0] value);
    bit  read;
    $assertoff(0, "tb.dut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscDataOut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscIv");
    if (!uvm_hdl_check_path(intf_mul_array[target])) begin
      `uvm_fatal("fi_control_if", $sformatf("PATH NOT EXISTING %m"))
    end
    // read the value currently of bit 0
    uvm_hdl_read(intf_mul_array[target], read);
    // flip bit to make sure we don't force the value currently on bus
    value[0] = !read;
    if (!uvm_hdl_force(intf_mul_array[target], value)) begin
      `uvm_error("fi_control_if", $sformatf("Was not able to force %s", intf_mul_array[target]))
    end
  endfunction


  function automatic void release_multi_bit(int target);
    uvm_hdl_release(intf_mul_array[target]);
    $asserton(0,"tb.dut");
  endfunction // release_single_bit



  ///////////////////////////////////
  // Fault inject coverage         //
  ///////////////////////////////////

  covergroup aes_ctrl_fsm_cg (int num_bins) with function sample(int target);
    // We want to see coverage per instance,
    // but as the code are copies of eachother
    // we don't need every instance to achieve 100% coverage
    // a total of 100% is enough so we set the option
    // to merge the coverage of the instances
    option.per_instance         = 0;
    option.name                 = "aes_ctrl_interleave_cg";
    type_option.merge_instances = 1;

    cp_target: coverpoint target
      {
         bins signal_target[] = {[0:num_bins-1]};
      }

    // A fault is injected in each state.  Ignore the error state because it is the result of
    // a fault and not a regular operating condition in which faults are expected to be handled.
    cp_state: coverpoint aes_ctrl_cs {
      ignore_bins error = {aes_pkg::CTRL_ERROR};
    }

    // Each target signal is faulted in each state.
    target_state_cross: cross cp_target, cp_state;
  endgroup // aes_ctrl_fsm_cg

  //aes_ctrl_fsm_cg my_cg = new(intf_array.size() + intf_mul_array.size() -1);
  `DV_FCOV_INSTANTIATE_CG(aes_ctrl_fsm_cg, 1'b1,(intf_array.size() + intf_mul_array.size()) )


  function automatic void cg_aes_ctrl_fsm_sample(int target);
    aes_ctrl_fsm_cg_inst.sample(target);
  endfunction // cg_aes_ctrl_fsm_sample


endinterface
