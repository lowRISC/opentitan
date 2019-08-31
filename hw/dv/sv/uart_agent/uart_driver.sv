// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_driver extends uvm_driver #(uart_item);
  `uvm_component_utils(uart_driver)

  uart_agent_cfg cfg;

  `uvm_component_new

  task run_phase(uvm_phase phase);
    reset_signals();
    get_and_drive();
  endtask

  // Resets signals.
  virtual task reset_signals();
    cfg.vif.uart_rx <= 1'b1;
  endtask

  // Sets the value of rx after randomly glitching for 10% of uart clk
  task set_rx(input bit val);
    uint glitch_ns = uint'(cfg.vif.uart_clk_period_ns * 0.1);
    repeat(glitch_ns) begin
      cfg.vif.uart_rx <= $urandom_range(0, 1);
      #1ns;
    end
    cfg.vif.uart_rx <= val;
  endtask

  // Drives transfers.
  virtual task get_and_drive();
    bit send_data[];
    forever begin
      seq_item_port.get(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("starting to send rx item: %0s", rsp.sprint()), UVM_HIGH)
      // we send parity if enabled or if overridden in the req
      // 1 start + 8 data + 1 parity (if enabled) + 1 stop
      if (cfg.en_parity ^ req.ovrd_en_parity) begin
        send_data = new[11];
        {<<{send_data}} = {req.stop_bit, req.parity, req.data, req.start_bit};
      end
      else begin
        send_data = new[10];
        {<<{send_data}} = {req.stop_bit, req.data, req.start_bit};
      end
      // send data on uart_rx
      for (int i = 0; i < send_data.size(); i++) begin
        set_rx(send_data[i]);
        @(cfg.vif.drv_rx_mp.drv_rx_cb);
      end
      `uvm_info(`gfn, $sformatf("finished sending rx item: %0s", rsp.sprint()), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end
  endtask

endclass
