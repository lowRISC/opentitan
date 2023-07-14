// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test will program DUT in illegal mode
// then trigger start to see if triggering
// an illegal configuration can be forced

// scoreboard is disabled for this test
class aes_manual_config_err_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_manual_config_err_vseq)

  `uvm_object_new
  aes_message_item   my_message;
  bit                rst_set;
  clear_t            clear      = 2'b00;
  aes_seq_item       cfg_item   = new();
  aes_seq_item       data_item  = new();
  status_t           status;

  task body();
    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES MANUAL/ERROR SEQUENCE |----\n %s",
                              cfg.convert2string()), UVM_LOW)

    fork
      // start sideload (even if not used)
      start_sideload_seq();
    join_none

    // generate list of messages //
    generate_message_queue();

    // process all messages //
    while (message_queue.size() > 0 ) begin
      `uvm_info(`gfn, $sformatf("Starting New Message - messages left %d",
                                 message_queue.size() ), UVM_MEDIUM)

      my_message = message_queue.pop_back();
      generate_aes_item_queue(my_message);

      cfg_item = aes_item_queue.pop_back();

      // Wait until the DUT is idle. This is required to start the configuration.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // Configure the DUT. Depending on the configuration, this might trigger a PRNG reseed
      // operation.
      setup_dut(cfg_item);

      // Wait until the DUT is idle. This is required to provide key and IV.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // Provide key, IV and data. This will also reconfigure the DUT with the illegal mode
      // setting. This might trigger a PRNG reseed operation again. The test configures the DUT
      // in automatic mode, i.e., upon providing key, IV and data, it would automatically start
      // to produce output if the configuration was valid.
      data_item = aes_item_queue.pop_back();
      write_data_key_iv(cfg_item, data_item, 1, 0, 0, 0, rst_set);

      // Wait until the DUT is idle.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));

      // Try to manually start the DUT. As it's configured in automatic mode, this should have
      // no effect.
      trigger();

      // Check that during a fixed time window, the DUT does not become busy and doesn't not
      // produce valid output. Both would mean that we were able to trigger an encryption or
      // decryption operation with an illegal mode setting.
      for (int nn = 0; nn < 20; nn++) begin
        csr_rd(.ptr(ral.status), .value(status), .blocking(1));
        if (!status.idle || status.output_valid) begin
          `uvm_fatal(`gfn, $sformatf("WAS ABLE TO TRIGGER OPERATION WITH ILLEGAL MODE"))
        end
        cfg.clk_rst_vif.wait_clks(5);
      end
    end
  endtask : body
endclass
