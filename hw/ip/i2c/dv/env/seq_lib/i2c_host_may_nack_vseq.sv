// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_host_may_nack_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_may_nack_vseq)
  `uvm_object_new

  virtual task i2c_init(if_mode_e mode = Host);
    super.i2c_init();
    // Mask some interrupts that are just noise for this test.
    ral.intr_enable.fmt_threshold.set(1'b0);
    ral.intr_enable.tx_threshold.set(1'b0);
    ral.intr_enable.sda_interference.set(1'b0);
    ral.intr_enable.scl_interference.set(1'b0);
    ral.intr_enable.sda_unstable.set(1'b0);
    ral.intr_enable.stretch_timeout.set(1'b0);
    csr_update(ral.intr_enable);

    // Enable the 'nak' timeout feature, but with a longer timeout than our handler latency.
    ral.host_nack_handler_timeout.en.set(1'b1);
    ral.host_nack_handler_timeout.val.set(30'd5000);
    csr_update(ral.host_nack_handler_timeout);
  endtask

  // Override the base vseq method to configure an agent which may sometime NACK
  virtual task agent_init(if_mode_e mode = Device);
    i2c_target_may_nack_seq may_nack_seq;

    case (mode)
      Device: begin
        `uvm_create_obj(i2c_target_may_nack_seq, may_nack_seq)
        fork may_nack_seq.start(p_sequencer.i2c_sequencer_h); join_none
      end
      Host:    `uvm_fatal(`gfn, "This vseq requires the agent to be in TARGET-Mode!")
      default: `uvm_fatal(`gfn, "Invalid 'if_mode'!")
    endcase
  endtask : agent_init

endclass : i2c_host_may_nack_vseq
