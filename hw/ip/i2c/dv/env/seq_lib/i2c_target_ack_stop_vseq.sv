// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
          wait(cfg.sent_ack_stop > 0);

          forever begin
            wait(cfg.m_i2c_agent_cfg.ack_stop_det);
            `uvm_info("ack_stop_seq", $sformatf("assa ack_stop rcvd %0d", cfg.rcvd_ack_stop),
                      UVM_MEDIUM)
            clear_interrupt(UnexpStop);
            cfg.m_i2c_agent_cfg.ack_stop_det = 0;
            cfg.rcvd_ack_stop++;
          end
        end
      join_any
      disable fork;
    end join
  endtask
endclass
