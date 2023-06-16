// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// AES prng reseeding test vseq

class aes_reseed_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_reseed_vseq)

  `uvm_object_new
  aes_message_item my_message;
  bit finished_all_msgs = 0;
  rand bit [7:0][31:0] init_key[2];
  // Regular wait time - in the order of a block.
  int wait_timeout_cycles = 100;
  // Max wait time to accomodate long entropy delays and DUT stalls.
  int wait_timeout_cycles_max = 100000;

  task check_clearing_prng_reseed();
    // Wait for entropy_clearing_req to verify the reseeding is triggered.
    bit request_seen = 0;
    `uvm_info(`gfn, $sformatf("Checking that entropy_clearing_req goes high, currently %d",
        cfg.aes_reseed_vif.entropy_clearing_req), UVM_MEDIUM)
    `DV_SPINWAIT_EXIT(
        wait (cfg.aes_reseed_vif.entropy_clearing_req) request_seen = 1;,
        cfg.clk_rst_vif.wait_clks(wait_timeout_cycles);,
        "Timeout waiting for entropy_clearing_req")
    `DV_CHECK_EQ_FATAL(request_seen, 1'b1)
  endtask

  task check_masking_prng_reseed();
    // Wait for entropy_masking_req to go high to verify the reseeding is triggered.
    bit request_seen = 0;
    `uvm_info(`gfn, $sformatf("Checking that entropy_masking_req goes high, currently %d",
        cfg.aes_reseed_vif.entropy_masking_req), UVM_MEDIUM)
    `DV_SPINWAIT_EXIT(
        wait (cfg.aes_reseed_vif.entropy_masking_req) request_seen = 1;,
        cfg.clk_rst_vif.wait_clks(wait_timeout_cycles);,
        "Timeout waiting for entropy_masking_req")
    `DV_CHECK_EQ_FATAL(request_seen | finished_all_msgs, 1'b1)
    // Wait for entropy_masking_req to go low again to verify the reseeding finishes.
    request_seen = 0;
    `uvm_info(`gfn, $sformatf("Checking that entropy_masking_req goes low, currently %d",
        cfg.aes_reseed_vif.entropy_masking_req), UVM_MEDIUM)
    `DV_SPINWAIT_EXIT(
        wait (!cfg.aes_reseed_vif.entropy_masking_req) request_seen = 1;,
        cfg.clk_rst_vif.wait_clks(wait_timeout_cycles_max);,
        "Timeout waiting for entropy_masking_req")
    `DV_CHECK_EQ_FATAL(request_seen | finished_all_msgs, 1'b1)
  endtask

  task check_prng_reseed(bit exp_reseed);
    if (exp_reseed) begin
      // Check entropy_clearing_req to verify the reseeding is actually triggered.
      check_clearing_prng_reseed();
      if (`EN_MASKING) begin
        check_masking_prng_reseed();
      end
      // Wait for the DUT to become idle again. This happens once the reseed operation finishes.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    end else begin
      // No reseed operation is supposed to be triggered.
      cfg.clk_rst_vif.wait_clks(1);
      `DV_CHECK_EQ_FATAL(cfg.aes_reseed_vif.entropy_clearing_req |
                         cfg.aes_reseed_vif.entropy_masking_req, 1'b0)
    end
  endtask

  task check_reseed_rate();
    bit [BlockCtrWidth-1:0] block_ctr;
    bit [BlockCtrWidth-1:0] block_ctr_set_val = BlockCtrWidth'(3);
    bit cipher_crypt;
    bit cipher_out_valid;
    bit cipher_out_ready;
    string base_path = $sformatf("%s.%s",
        "tb.dut.u_aes_core.u_aes_control", // Control module
        "gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.u_aes_control_fsm"); // FSM instance
    string block_ctr_path = $sformatf("%s.gen_block_ctr.block_ctr_q", base_path);
    string cipher_crypt_path = $sformatf("%s.crypt", base_path);
    string cipher_out_valid_path = $sformatf("%s.cipher_out_valid_i", base_path);
    string cipher_out_ready_path = $sformatf("%s.cipher_out_ready_o", base_path);
    status_t status;
    bit block_done;

    if (`EN_MASKING) begin
      // Check paths to signals we need to probe.
      if (!uvm_hdl_check_path(block_ctr_path)) begin
        `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
      end
      if (!uvm_hdl_check_path(cipher_crypt_path)) begin
        `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
      end
      if (!uvm_hdl_check_path(cipher_out_valid_path)) begin
        `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
      end
      if (!uvm_hdl_check_path(cipher_out_ready_path)) begin
        `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
      end
    end

    while (!finished_all_msgs) begin
      // Wait for next negative clock edge.
      #1step;
      @(cfg.clk_rst_vif.cbn);

      if (`EN_MASKING) begin
        // Read the block counter.
        `DV_CHECK_FATAL(uvm_hdl_read(block_ctr_path, block_ctr))

        // Force a lower value to get more more action.
        if (block_ctr == 8188 || // Speed up testing of the PER_8K setting.
            block_ctr == 60) begin // Speed up testing of the PER_64 setting.
          `uvm_info(`gfn, $sformatf("Lowering block counter from %0d to %0d to speed up testing",
              block_ctr, block_ctr_set_val), UVM_LOW)
          `DV_CHECK(uvm_hdl_force(block_ctr_path, block_ctr_set_val));
          cfg.clk_rst_vif.wait_clks(1);
          `DV_CHECK_FATAL(uvm_hdl_release(block_ctr_path))

        end else if (block_ctr == 0) begin
          // Check whether the DUT is actually busy. Unless it's doing a block operation, no reseed
          // operation is getting triggered.
          csr_rd(.ptr(ral.status), .value(status), .blocking(1));
          `DV_CHECK_FATAL(uvm_hdl_read(cipher_crypt_path, cipher_crypt))
          if (!status.idle && cipher_crypt) begin
            // Check entropy_masking_req to verify the reseeding is actually triggered.
            check_masking_prng_reseed();

            // Wait for the DUT to finish the current block.
            block_done = 0;
            `DV_SPINWAIT_EXIT(
                while (!block_done) begin
                  `DV_CHECK_FATAL(uvm_hdl_read(cipher_out_valid_path, cipher_out_valid))
                  `DV_CHECK_FATAL(uvm_hdl_read(cipher_out_ready_path, cipher_out_ready))
                  if (cipher_out_valid && cipher_out_ready) begin
                    block_done = 1;
                  end
                  cfg.clk_rst_vif.wait_clks(1);
                end;,
                cfg.clk_rst_vif.wait_clks(wait_timeout_cycles_max);,
                "Timeout waiting for block to finish")
          end
        end

      end else begin
        // There is no masking PRNG and hence no block counter. entropy_masking_req must never be
        // asserted.
        `DV_CHECK_EQ_FATAL(cfg.aes_reseed_vif.entropy_masking_req, 1'b0)
      end
    end
  endtask

  task body();
    bit sideload_valid;
    string sideload_valid_path = "tb.dut.keymgr_key_i.valid";
    bit sideload_enabled;
    bit sideload_setup_done;
    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES MAIN SEQUENCE |----\n %s",
                              cfg.convert2string()), UVM_LOW)

    fork
      // generate list of messages //
      generate_message_queue();
      // start sideload (even if not used)
      start_sideload_seq();
    join_any

    // Trigger reseed by manually setting the PRNG_RESEED bit in the TRIGGER register.
    `uvm_info(`gfn, "Triggering PRNG reseed via trigger register", UVM_LOW)
    prng_reseed();
    check_prng_reseed(.exp_reseed(1'b1));

    // Trigger reseed by writing a new key to the initial key registers. In case
    // KEY_TOUCH_FORCES_RESEED is not set, no reseed operation is supposed to be triggered. The
    // default configuration written after reset is not using the sideload interface for the key.
    `uvm_info(`gfn, "Potentially triggering PRNG reseed by writing a new key", UVM_LOW)
    `DV_CHECK_STD_RANDOMIZE_FATAL(init_key)
    // Wait for the DUT to be idle before writing the key.
    csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    write_key(init_key, 1'b0);
    check_prng_reseed(.exp_reseed(cfg.do_reseed));

    // Trigger reseed by loading a new key via sideload interface. In case KEY_TOUCH_FORCES_RESEED
    // is not set, no reseed operation is supposed to be triggered.
    // Wait for the DUT to be idle before enabling sideload.
    `uvm_info(`gfn, "Potentially triggering PRNG reseed by providing a new sideload key", UVM_LOW)
    if (!uvm_hdl_check_path(sideload_valid_path)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end
    sideload_setup_done = 0;
    while (!sideload_setup_done) begin
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // Make sure sideload is disabled.
      set_sideload(1'b0);
      sideload_enabled = 1'b0;
      // Wait for sideload key to be valid before enabling sideload.
      sideload_valid = 0;
      `DV_SPINWAIT_EXIT(
        while (!sideload_valid) begin
          cfg.clk_rst_vif.wait_clks(1);
          `DV_CHECK_FATAL(uvm_hdl_read(sideload_valid_path, sideload_valid))
        end,
        cfg.clk_rst_vif.wait_clks(wait_timeout_cycles);,
        "Timeout waiting for valid sideload key")
      fork
        // Enable sideload.
        begin
          set_sideload(1'b1);
          sideload_enabled = 1'b1;
        end
        // Detect if the sideload valid bit gets de-asserted while trying to enable sideload.
        begin
          while (sideload_valid && !sideload_enabled) begin
            cfg.clk_rst_vif.wait_clks(1);
            `DV_CHECK_FATAL(uvm_hdl_read(sideload_valid_path, sideload_valid))
          end
        end
      join

      // If the sideload valid bit got de-asserted again before fully enabling sideload, the key
      // did not get loaded and we have to repeat the setup procedure. Otherwise, sideload was
      // enabled successfully.
      if (sideload_valid) begin
        sideload_setup_done = 1;
      end
    end

    // Sideload got enabled with a valid sideload key present. This must trigger a reseed in case
    // KEY_TOUCH_FORCES_RESEED is set.
    check_prng_reseed(.exp_reseed(cfg.do_reseed));

    // Test that the PRNGs are reseeded at the proper rate during message processing.
    `uvm_info(`gfn, "Testing automatic / block counter based reseeding of the masking PRNG",
        UVM_LOW)
    fork
      basic: begin
        // Kick off the message processing.
        send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);
        finished_all_msgs = 1;
      end

      // Check that the reseeds happens when the counter expires.
      check_reseed_rate();
    join_any

  endtask : body
endclass
