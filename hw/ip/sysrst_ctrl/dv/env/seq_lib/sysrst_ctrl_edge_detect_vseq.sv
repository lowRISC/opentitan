// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will detect the edge transition on input keys
// and raise an interrupt
class sysrst_ctrl_edge_detect_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_edge_detect_vseq)

  `uvm_object_new

    uvm_reg_data_t rdata;
   
   task body();

      `uvm_info(`gfn, "Starting the body from edge_detect_vseq", UVM_LOW)

       // Select the inputs and their transition
       csr_wr(ral.key_intr_ctl, 'he0e);

       // Set the key interrupt debounce timer value
       csr_wr(ral.key_intr_debounce_ctl, 'h15);

      repeat ($urandom_range(1,3)) begin
        // Press the pwrb_in input key
        cfg.vif.key0_in = 1;
        cfg.vif.key1_in = 1;
        cfg.vif.key2_in = 1;
        #50us;
        cfg.vif.key0_in = 0;
        cfg.vif.key1_in = 0;
        cfg.vif.key2_in = 0;
        #50us;
      end

       // Wait for the timer to reach the value configured to debounce_timer
       #100us;

       csr_rd(ral.key_intr_status, rdata);
       `uvm_info(`gfn, $sformatf("Reading status register:%0h", rdata), UVM_NONE)

       csr_wr(ral.key_intr_status, rdata);

       #50us;
       csr_rd(ral.key_intr_status, rdata);
       `uvm_info(`gfn, $sformatf("Cleared the interrupt register:%0h", rdata), UVM_NONE)
       
   endtask : body

endclass : sysrst_ctrl_auto_blk_key_output_vseq

