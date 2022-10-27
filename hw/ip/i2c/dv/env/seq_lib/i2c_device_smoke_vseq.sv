// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class i2c_device_smoke_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_device_smoke_vseq)
  `uvm_object_new

  virtual task body();
    i2c_base_seq m_i2c_host_seq;
    // Intialize dut in device mode and agent in host mode

    initialization(Device);
    program_registers();
    //for (int i = 1; i <= num_trans; i++) begin
    for (int i = 1; i <= 1; i++) begin
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      `uvm_create_on(m_i2c_host_seq, p_sequencer.i2c_sequencer_h)
      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_i2c_host_seq,
                                     data_q.size() <= 16;)
      `uvm_send(m_i2c_host_seq)
    end
  endtask : body


endclass : i2c_device_smoke_vseq
