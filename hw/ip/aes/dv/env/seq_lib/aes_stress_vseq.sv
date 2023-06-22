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

    // Create one thread such that we can kill all its children without unwanted side effects on the
    // caller.
    fork
      begin

        fork
          // generate list of messages //
          generate_message_queue();
          // start sideload (even if not used)
          start_sideload_seq();
        join_any
        // process all messages //
        send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);

      end
    // Kill all children.
    disable fork;
    join

  endtask : body
endclass
