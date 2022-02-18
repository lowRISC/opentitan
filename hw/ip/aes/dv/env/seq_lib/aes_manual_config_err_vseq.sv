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

      // wait for DUT IDLE
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // configure dut
      setup_dut(cfg_item);
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));

      // program illegal mode
      data_item = aes_item_queue.pop_back();
      write_data_key_iv(cfg_item, data_item, 1,
                        0, 0, 0, rst_set);

      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      trigger();
      for (int nn = 0; nn <10; nn++) begin
        csr_rd(.ptr(ral.status), .value(status), .blocking(1));
        if (!status.idle && !status.alert_fatal_fault)
          `uvm_fatal(`gfn, $sformatf("WAS ABLE TO TRIGGER OPERATION WITH ILLEGAL MODE"))

        cfg.clk_rst_vif.wait_clks(25);
      end
    end
  endtask : body
endclass
