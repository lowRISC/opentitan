// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic main test vseq
class aes_stress_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_stress_vseq)

  `uvm_object_new
  aes_message_item my_message;

  task body();
    `uvm_info(`gfn, $sformatf("\n\t ----| STARTING AES MAIN SEQUENCE |----\n"), UVM_LOW);
    `uvm_info(`gfn, $sformatf("\n\t cfg item \n %s", cfg.convert2string()), UVM_LOW)

    // generate list of messages //
    generate_message_queue();
    // process all messages //
    while (message_queue.size() > 0) begin
      // get next message from queue
      my_message = new();
      my_message = message_queue.pop_back();

      // for this message generate configuration
      // and data items (split message into blocks)
      generate_aes_item_queue(my_message);
      // setup and transmit based on settings
      if (my_message.manual_operation) begin
        transmit_message_manual_op();
      end else begin
        transmit_message_with_rd_back();
      end
    end
  endtask : body
endclass
