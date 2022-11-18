// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_timeout_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_timeout_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.min_data = 10;
    cfg.max_data = 20;
    num_trans = 5;
    expected_intr[HostTimeout] = 1;

    // Set to lower value than default (0xffff)
    host_timeout_ctrl = 32'd100;
    cfg.m_i2c_agent_cfg.host_scl_pause_cyc = 100;
  endtask

  virtual task body();
    fork
       begin
         super.body();
       end
       begin
         int delay;
          int round = 0;

         cfg.clk_rst_vif.wait_for_reset(.wait_negedge(0));
         repeat (5) begin
            round++;

            delay = $urandom_range(10, 100);
         `uvm_info("drv_pause", $sformatf("round %0d begin", round), UVM_MEDIUM)
         #(delay * 1us);
         `uvm_info("drv_pause", "set req", UVM_MEDIUM)
         cfg.m_i2c_agent_cfg.host_scl_pause_req = 1;
         `DV_WAIT(cfg.m_i2c_agent_cfg.host_scl_pause_ack,,
                  cfg.spinwait_timeout_ns, "drv_pause")
         `uvm_info("drv_pause", "got ack", UVM_MEDIUM)
         `DV_WAIT(cfg.intr_vif.pins[HostTimeout] === 1,,
                  cfg.spinwait_timeout_ns, "drv_pause")
          clear_interrupt(HostTimeout);
            `uvm_info("drv_pause", $sformatf("round %0d end", round), UVM_MEDIUM)
          end
       end
    join
  endtask
endclass
