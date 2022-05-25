// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// AES prng reseeding test vseq
`define BLOCK_CTR_WIDTH 13

class aes_reseed_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_reseed_vseq)

  `uvm_object_new
  aes_message_item      my_message;
  rand bit [7:0] [31:0] init_key[2];

  task check_reseed_in_progress(logic entropy_req, int wait_timeout_cycles, string req_name);
    // wait on entropy_clearing_req/entropy_masking_req to verify the reseeding is triggered
    `DV_SPINWAIT_EXIT(
      wait(entropy_req);,
      cfg.clk_rst_vif.wait_clks(wait_timeout_cycles);,
      $sformatf("Timeout waiting for %0s for triggering reseed", req_name))
  endtask // check_reseed_in_progress

  task body();
    bit    do_b2b   = 0;
    bit    sideload = 1;
    int    wait_timeout_cycles = 100;
    string set_val_path;
    string base_path = "tb.dut.u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i";
    bit [`BLOCK_CTR_WIDTH-1: 0] set_val;

    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES MAIN SEQUENCE |----\n %s",
                              cfg.convert2string()), UVM_LOW)

    fork
      // generate list of messages //
      generate_message_queue();
      // start sideload (even if not used)
      start_sideload_seq();
    join_any

    // trigger reseed with prng_reseed
    prng_reseed();
    // wait on entropy_clearing_req to verify the reseeding is actually triggered
    check_reseed_in_progress(cfg.aes_reseed_vif.entropy_clearing_req, wait_timeout_cycles,
                             "entropy_clearing_req");
    if (`EN_MASKING) begin
      check_reseed_in_progress(cfg.aes_reseed_vif.entropy_masking_req, wait_timeout_cycles,
                               "entropy_masking_req");
    end

    // trigger reseed by writing a new key
    csr_wr(.ptr(ral.ctrl_aux_shadowed), .value(1'b1));
    `DV_CHECK_STD_RANDOMIZE_FATAL(init_key)
    write_key(init_key, do_b2b);
    // wait on entropy_clearing_req to verify the reseeding is actually triggered
    check_reseed_in_progress(cfg.aes_reseed_vif.entropy_clearing_req, wait_timeout_cycles,
                             "entropy_clearing_req");
    if (`EN_MASKING) begin
      check_reseed_in_progress(cfg.aes_reseed_vif.entropy_masking_req, wait_timeout_cycles,
                               "entropy_masking_req");
    end

    // trigger reseed in sideload mode
    // enable sideload
    set_sideload(sideload);
    // wait on entropy_clearing_req to verify the reseeding is actually triggered
    check_reseed_in_progress(cfg.aes_reseed_vif.entropy_clearing_req, wait_timeout_cycles,
                             "entropy_clearing_req");
    if (`EN_MASKING) begin
      check_reseed_in_progress(cfg.aes_reseed_vif.entropy_masking_req, wait_timeout_cycles,
                               "entropy_masking_req");
    end

    // reseed rate test
    // write reseed rate
    ral.ctrl_shadowed.prng_reseed_rate.set(cfg.reseed_rate);
    csr_update(.csr(ral.ctrl_shadowed));
    // trigger reseed with prng_reseed
    prng_reseed();
    if (`EN_MASKING) begin
      // set the block counter to a low value to speed up the reseed rate test
      set_val_path = {base_path, ".u_aes_control_fsm.gen_block_ctr.block_ctr_set_val"};
      set_val = `BLOCK_CTR_WIDTH'(4);
      if (cfg.aes_reseed_vif.prng_reseed_rate != PER_1) begin
        if (!uvm_hdl_check_path(set_val_path)) begin
          `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
        end else begin
          `DV_CHECK(uvm_hdl_force(set_val_path, set_val));
        end
      end
    end
    // process all messages //
    send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);

  endtask : body
endclass
