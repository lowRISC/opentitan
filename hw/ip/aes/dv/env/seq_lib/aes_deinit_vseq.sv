// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Will generate a few messages to process
// will clear the read data and make sure read data
// is no longer present.

// scoreboard is disabled for this test
class aes_deinit_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_deinit_vseq)

  `uvm_object_new
  aes_message_item   my_message;
  bit  [3:0][31:0]   data,prev_data;
  bit                rst_set;
  bit                back2back = 0;
  clear_t            clear     = 2'b00;
  string             txt ="";
  status_t           status;

  task body();
    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES DE-INIT SEQUENCE |----\n %s",
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

      send_msg(my_message.manual_operation, my_message.sideload_en,
               cfg.unbalanced, cfg.read_prob, cfg.write_prob, rst_set);

      // read output //
      read_data(prev_data, back2back);
      read_data(data, back2back);

      if (data != prev_data) begin
        txt = "Read data ERROR: read data and previous data did not match";
        txt = {txt, $sformatf("read data \t 0x%0h", data) };
        txt = {txt, $sformatf("prev data \t 0x%0h", prev_data) };
        `uvm_fatal(`gfn, $sformatf("%s", txt))
      end

      // clear the output registers
      clear.dataout = 1'b1;
      clear_regs(clear);
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      read_data(data, back2back);

      if ((data == prev_data) || (data == 32'h00000000)) begin
        txt = "\n Read data ERROR: the output register was not cleared correctly";
        txt = {txt, $sformatf("\n read data \t 0x%0h", data) };
        txt = {txt, $sformatf("\n prev data \t 0x%0h", prev_data) };
        `uvm_fatal(`gfn, $sformatf("%s", txt))
      end
    end

    // read IV
    read_iv(prev_data, back2back);

    // now clear key/iv/data and try to manually trigger an operation
    clear.key_iv_data_in = 1'b1;
    clear_regs(clear);
    csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    // make sure that IV was cleared
    read_iv(data, back2back);

    if ((data == prev_data) || (data == 32'h00000000)) begin
      txt = "\n IV ERROR: the output register was not cleared correctly";
      txt = {txt, $sformatf("\n Current IV: \t 0x%0h", data) };
      txt = {txt, $sformatf("\n prev IV:    \t 0x%0h", prev_data) };
      `uvm_fatal(`gfn, $sformatf("%s", txt))
    end

    // make sure we cant trigger an operation
    trigger();
    csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    for (int nn = 0; nn <10; nn++) begin
        csr_rd(.ptr(ral.status), .value(status), .blocking(1));
        if ((!status.idle && !status.alert_fatal_fault) || status.output_valid)
          `uvm_fatal(`gfn, $sformatf("WAS ABLE TO TRIGGER OPERATION AFTER CLEAR MODE"))

        cfg.clk_rst_vif.wait_clks(25);
      end
  endtask : body
endclass
