// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_driver extends dv_base_driver #(uart_item, uart_agent_cfg);
  `uvm_component_utils(uart_driver)

  `uvm_component_new

  task run_phase(uvm_phase phase);
    reset_signals();
    get_and_drive();
  endtask

  // Resets signals.
  virtual task reset_signals();
    cfg.vif.reset_uart_rx();
  endtask

  // Sets the value of rx after randomly glitching for 10% of uart clk
  task set_rx(input bit val);
    uint glitch_ns = uint'(cfg.vif.uart_clk_period_ns * cfg.get_uart_period_glitch_pct() / 100);
    repeat (glitch_ns) begin
      if (!cfg.under_reset) begin
        cfg.vif.uart_rx <= $urandom_range(0, 1);
        #1ns;
      end
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
      if (!cfg.under_reset) begin
        `uvm_info(`gfn, $sformatf("starting to send rx item: %0s", rsp.sprint()), UVM_HIGH)
        // we send parity if enabled or if overridden in the req
        if (cfg.en_parity ^ req.ovrd_en_parity) begin
          send_data = new[NUM_UART_XFER_BITS_WO_PARITY + 1]; // + 1 for parity bit
          {<<{send_data}} = {req.stop_bit, req.parity, req.data, req.start_bit};
        end
        else begin
          send_data = new[NUM_UART_XFER_BITS_WO_PARITY];
          {<<{send_data}} = {req.stop_bit, req.data, req.start_bit};
        end
        // send data on uart_rx
        for (int i = 0; i < send_data.size(); i++) begin
          set_rx(send_data[i]);
          wait_uart_rx_cycle();
        end
        `uvm_info(`gfn, $sformatf("finished sending rx item: %0s", rsp.sprint()), UVM_HIGH)
      end
      if (cfg.under_reset) begin // under_reset
        `uvm_info(`gfn, $sformatf("Reset happens and drop rx item: %0s", rsp.sprint()), UVM_HIGH)
      end
      seq_item_port.put_response(rsp);
    end
  endtask

  virtual task wait_uart_rx_cycle();
    fork
      begin : isolation_fork
        fork
          begin
            wait(cfg.under_reset);
          end
          begin
            @(cfg.vif.drv_rx_mp.drv_rx_cb);
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

endclass
