// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq stimulates the assertion of the unexp_stop interrupt (DUT-Target mode), which should
// trigger when a STOP condition is received without an immediately-preceding NACK during a READ
// transfer.
//
class i2c_target_ack_stop_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_ack_stop_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    expected_intr[UnexpStop] = 1;
    cfg.m_i2c_agent_cfg.allow_ack_stop = 1;
  endtask

  virtual task body();
    fork begin
      fork
        super.body();
        begin
          cfg.clk_rst_vif.wait_for_reset(.wait_negedge(0));

          forever begin
            wait(cfg.m_i2c_agent_cfg.ack_stop_det);
            cfg.m_i2c_agent_cfg.ack_stop_det = 0;
            // When the monitor signals the ack-stop stimulus has occurred, we can then check
            // that the DUT has correctly asserted it's 'unexp_stop' interrupt.
            check_one_intr(UnexpStop, 1);
            clear_interrupt(UnexpStop);
          end
        end
      join_any
      disable fork;
    end join
  endtask

  // This task is invoked by the stop_target_interrupt_handler() code to generate one final
  // transaction which ends via the ack-the-stop condition.
  task send_ack_stop();
    i2c_target_base_seq m_i2c_host_seq;
    i2c_item txn_q[$];
    cfg.rs_pct = 0;
    cfg.wr_pct = 0;

    force_ack = 1; // Force the txn we're about to generate to end with an ACK.

    `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
    generate_agent_controller_stimulus(m_i2c_host_seq.req_q);
    m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
    sent_txn_cnt++;
  endtask


endclass
