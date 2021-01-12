// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic main test vseq
class aes_stress_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_stress_vseq)

  `uvm_object_new
  aes_message_item my_message;

  task body();
    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES MAIN SEQUENCE |----\n %s",
               cfg.convert2string()), UVM_LOW)

    // generate list of messages //
    generate_message_queue();
    // process all messages //
    send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);
  endtask : body
endclass
