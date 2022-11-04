// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic smoke test vseq
class i2c_target_smoke_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_target_smoke_vseq)
  `uvm_object_new

  virtual task body();
    i2c_target_base_seq m_i2c_host_seq;
    i2c_item txn_q[$];

    // Intialize dut in device mode and agent in host mode
    initialization(Device);
    `uvm_info("cfg_summary", $sformatf("target_addr0:0x%x target_addr1:0x%x num_trans:%0d",
                             target_addr0, target_addr1, num_trans), UVM_MEDIUM)
    print_time_property();

    fork
      begin
        for (int i = 0; i < num_trans; i++) begin
          get_timing_values();
          if (i > 0) begin
            // wait for previous stop before program a new timing param.
            @(cfg.m_i2c_agent_cfg.got_stop);
          end
          program_registers();

          `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
          create_txn(txn_q);
          fetch_txn(txn_q, m_i2c_host_seq.req_q);
          m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
        end
      end
      begin
        process_acq();
      end
      begin
        process_txq();
      end
    join_none
  endtask : body

endclass : i2c_target_smoke_vseq
