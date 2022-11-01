// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// target specific signals inside the cipher core FSM
interface fi_cipher_if
  import uvm_pkg::*;
  (
   input logic clk_i,
   input logic rst_ni
   );

  `include "dv_fcov_macros.svh"
  // get bind path to module
  string       par_hier = dv_utils_pkg::get_parent_hier($sformatf("%m"), 2);

  // single bit forces
  string intf_array[] = {
    $sformatf("%s.%s", par_hier, "in_valid_i"),
    $sformatf("%s.%s", par_hier, "in_ready_o"),
    $sformatf("%s.%s", par_hier, "out_valid_o"),
    $sformatf("%s.%s", par_hier, "out_ready_i"),
    $sformatf("%s.%s", par_hier, "state_we_o"),
    $sformatf("%s.%s", par_hier, "sub_bytes_en_o"),
    $sformatf("%s.%s", par_hier, "sub_bytes_out_req_i"),
    $sformatf("%s.%s", par_hier, "sub_bytes_out_ack_o"),
    $sformatf("%s.%s", par_hier, "key_full_we_o"),
    $sformatf("%s.%s", par_hier, "key_dec_we_o"),
    $sformatf("%s.%s", par_hier, "key_expand_en_o"),
    $sformatf("%s.%s", par_hier, "key_expand_out_req_i"),
    $sformatf("%s.%s", par_hier, "key_expand_out_ack_o"),
    $sformatf("%s.%s", par_hier, "crypt_q_i"),
    $sformatf("%s.%s", par_hier, "crypt_d_o"),
    $sformatf("%s.%s", par_hier, "dec_key_gen_q_i"),
    $sformatf("%s.%s", par_hier, "dec_key_gen_d_o")
   };

  // multi bit forces
  string intf_mul_array[] = {
    $sformatf("%s.%s", par_hier, "rnd_ctr_o"),
    $sformatf("%s.%s", par_hier, "rnd_ctr_q"),
    $sformatf("%s.%s", par_hier, "state_sel_o"),
    $sformatf("%s.%s", par_hier, "add_rk_sel_o"),
    $sformatf("%s.%s", par_hier, "key_full_sel_o"),
    $sformatf("%s.%s", par_hier, "key_dec_sel_o"),
    $sformatf("%s.%s", par_hier, "key_words_sel_o"),
    $sformatf("%s.%s", par_hier, "round_key_sel_o")
  };

  function automatic int get_if_size();
    return intf_array.size() + intf_mul_array.size();
  endfunction // get_if_size

  // check which array we need to access and force or releae
  function automatic void force_signal(int target, bit rel, bit [31:0] value);
    if (!rel) aes_cipher_fsm_cg_inst.sample(target);
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
      `uvm_fatal("fi_cipher_if", $sformatf("PATH NOT EXISTING %m"))
    end
    // read the value currently
    uvm_hdl_read(intf_array[target], read);
    // always announce we are forcing something
    `uvm_info("if_cipher_if",
       $sformatf(" I am forcing target %d %s, value %b",target, intf_array[target], !read),UVM_LOW);
    if (!uvm_hdl_force(intf_array[target],!read)) begin
      `uvm_error("fi_cipher_if", $sformatf("Was not able to force %s", intf_array[target]))
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
    `uvm_info("if_cipher_if",
       $sformatf(" I am forcing target %d %s, \n value: %0h",
                  target, intf_mul_array[target], value),UVM_LOW);
    if (!uvm_hdl_check_path(intf_mul_array[target])) begin
      `uvm_fatal("fi_cipher_if", $sformatf("PATH NOT EXISTING %m"))
    end
    // read the value currently of bit 0
    uvm_hdl_read(intf_mul_array[target], read);
    // flip bit to make sure we don't force the value currently on bus
    value[0] = !read;
    if (!uvm_hdl_force(intf_mul_array[target], value)) begin
      `uvm_error("fi_cipher_if", $sformatf("Was not able to force %s", intf_mul_array[target]))
    end
  endfunction


  function automatic void release_multi_bit(int target);
    uvm_hdl_release(intf_mul_array[target]);
    $asserton(0,"tb.dut");
  endfunction // release_single_bit



  ///////////////////////////////////
  // Fault inject coverage         //
  ///////////////////////////////////

  covergroup aes_cipher_fsm_cg (int num_bins) with function sample(int target);
    // We want to see coverage per instance,
    // but as the code are copies of eachother
    // we don't need every instance to achieve 100% coverage
    // a total of 100% is enough so we set the option
    // to merge the coverage of the instances
    option.per_instance         = 0;
    option.name                 = "aes_cipher_interleave_cg";
    type_option.merge_instances = 1;

    cp_target: coverpoint target
      {
         bins signal_target[] = {[0:num_bins-1]};
      }
  endgroup

  //aes_cipher_fsm_cg my_cg = new(intf_array.size() + intf_mul_array.size() -1);
  `DV_FCOV_INSTANTIATE_CG(aes_cipher_fsm_cg, 1'b1,(intf_array.size() + intf_mul_array.size()) )
endinterface
