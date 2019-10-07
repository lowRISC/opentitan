// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// TileLink device driver
// ---------------------------------------------
class tl_device_driver extends uvm_driver#(tl_seq_item);

  virtual tl_if  vif;
  tl_agent_cfg   cfg;

  `uvm_component_utils(tl_device_driver)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual tl_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NO_VIF", {"virtual interface must be set for:",
        get_full_name(),".vif"});
    end
    if (!uvm_config_db#(tl_agent_cfg)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal("NO_CFG", {"cfg must be set for:", get_full_name(),".cfg"});
    end
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    wait_for_reset_done();
    fork
      a_channel_thread();
      d_channel_thread();
    join_none
  endtask : run_phase

  virtual task wait_for_reset_done();
    vif.device_cb.d2h.d_valid <= 1'b0;
    vif.device_cb.d2h.a_ready <= 1'b0;
    @(posedge vif.device_cb.rst_n);
  endtask : wait_for_reset_done

  virtual task a_channel_thread();
    int unsigned ready_delay;
    forever begin
      ready_delay = $urandom_range(cfg.a_ready_delay_min, cfg.a_ready_delay_max);
      repeat(ready_delay) @(vif.device_cb);
      vif.device_cb.d2h.a_ready <= 1'b1;
      @(vif.device_cb);
      vif.device_cb.d2h.a_ready <= 1'b0;
    end
  endtask

  virtual task d_channel_thread();
    bit req_found;
    tl_seq_item rsp;
    forever begin
      int unsigned d_valid_delay;
      seq_item_port.get_next_item(rsp);
      if (cfg.use_seq_item_d_valid_delay) begin
        d_valid_delay = rsp.d_valid_delay;
      end else begin
        d_valid_delay = $urandom_range(cfg.d_valid_delay_min, cfg.d_valid_delay_max);
      end
      repeat (d_valid_delay) @(vif.device_cb);
      vif.device_cb.d2h.d_valid  <= 1'b1;
      vif.device_cb.d2h.d_opcode <= rsp.d_opcode;
      vif.device_cb.d2h.d_data   <= rsp.d_data;
      vif.device_cb.d2h.d_source <= rsp.d_source;
      vif.device_cb.d2h.d_param  <= rsp.d_param;
      vif.device_cb.d2h.d_error  <= rsp.d_error;
      vif.device_cb.d2h.d_sink   <= rsp.d_sink;
      vif.device_cb.d2h.d_user   <= rsp.d_user;
      vif.device_cb.d2h.d_size   <= rsp.d_size;
      @(vif.device_cb);
      while(!vif.device_cb.h2d.d_ready) @(vif.device_cb);
      vif.device_cb.d2h.d_valid <= 1'b0;
      seq_item_port.item_done();
    end
  endtask : d_channel_thread

endclass
