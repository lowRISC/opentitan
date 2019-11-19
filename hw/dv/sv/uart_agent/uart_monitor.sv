// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


class uart_monitor extends dv_base_monitor#(
    .ITEM_T (uart_item),
    .CFG_T  (uart_agent_cfg),
    .COV_T  (uart_agent_cov)
  );
  `uvm_component_utils(uart_monitor)

  bit obj_raised[uart_dir_e];

  // Analysis port for the collected transfer.
  uvm_analysis_port #(uart_item) tx_analysis_port;
  uvm_analysis_port #(uart_item) rx_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tx_analysis_port = new("tx_analysis_port", this);
    rx_analysis_port = new("rx_analysis_port", this);
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      fork
        collect_tx_data();
        collect_rx_data();
        drive_tx_clk();
        drive_rx_clk();
        wait(cfg.under_reset);
      join_any
      disable fork;

      if (cfg.under_reset) process_reset();
    end
  endtask

  virtual task collect_tx_data();
    uart_item item;
    forever begin
      if (cfg.vif.uart_tx === 1'b0 && cfg.en_tx_monitor == 1) begin
        // 1 start + 8 data + 1 parity (if enabled) + 1 stop
        cfg.vif.uart_tx_clk_pulses = NUM_UART_XFER_BITS_WO_PARITY + cfg.en_parity;
        process_objections(UartTx, 1);
        item = uart_item::type_id::create("item");
        // get the start bit
        @(cfg.vif.mon_tx_mp.mon_tx_cb);
        `uvm_info(`gtn, $sformatf("tx start bit %0b", cfg.vif.uart_tx), UVM_DEBUG)
        item.start_bit = cfg.vif.uart_tx;
        // get the data bits
        for (int i = 0; i < 8; i++) begin
          @(cfg.vif.mon_tx_mp.mon_tx_cb);
          `uvm_info(`gtn, $sformatf("tx data bit[%0d] %0b", i, cfg.vif.uart_tx), UVM_DEBUG)
          item.data[i] = cfg.vif.uart_tx;
        end
        // get the parity bit
        if (cfg.vif.uart_tx_clk_pulses > 2) begin
          @(cfg.vif.mon_tx_mp.mon_tx_cb);
          `uvm_info(`gtn, $sformatf("tx parity bit %0b", cfg.vif.uart_tx), UVM_DEBUG)
          item.parity = cfg.vif.uart_tx;
          if (cfg.en_tx_checks && item.parity != `GET_PARITY(item.data, cfg.odd_parity)) begin
            `uvm_error(`gtn, "Parity failed")
          end
        end
        else item.parity = 1'b0;

        // get the stop bit
        @(cfg.vif.mon_tx_mp.mon_tx_cb);
        `uvm_info(`gtn, $sformatf("tx stop bit %0b", cfg.vif.uart_tx), UVM_DEBUG)
        item.stop_bit = cfg.vif.uart_tx;
        // check stop bit
        if (cfg.en_tx_checks && cfg.vif.uart_tx !== 1'b1) begin
          `uvm_error(`gtn, "No stop bit when expected!")
        end
        `uvm_info(`gtn, $sformatf("collected uart tx txn:\n%0s", item.sprint()), UVM_HIGH)
        tx_analysis_port.write(item);

        // wait for uart_tx_clk_pulses==0, otherwise, it may affect next transaction
        cfg.vif.wait_for_tx_idle();

        if (cfg.en_cov) cov.uart_cg.sample(UartTx, item);
        process_objections(UartTx, 0);
      end else begin
        @(cfg.vif.uart_tx);
      end
    end
  endtask

  virtual task collect_rx_data();
    uart_item item;
    forever begin
      if (cfg.vif.uart_rx === 1'b0 && cfg.en_rx_monitor == 1) begin
        process_objections(UartRx, 1);
        item = uart_item::type_id::create("item");
        cfg.vif.uart_rx_clk_pulses = NUM_UART_XFER_BITS_WO_PARITY + cfg.en_parity;
        // get the start bit
        @(cfg.vif.mon_rx_mp.mon_rx_cb);
        `uvm_info(`gtn, $sformatf("rx start bit %0b", cfg.vif.uart_rx), UVM_DEBUG)
        item.start_bit = cfg.vif.uart_rx;
        // get the data bits
        for (int i = 0; i < 8; i++) begin
          @(cfg.vif.mon_rx_mp.mon_rx_cb);
          `uvm_info(`gtn, $sformatf("rx data bit[%0d] %0b", i, cfg.vif.uart_rx), UVM_DEBUG)
          item.data[i] = cfg.vif.uart_rx;
        end
        // get the parity bit
        if (cfg.vif.uart_rx_clk_pulses > 2) begin
          @(cfg.vif.mon_rx_mp.mon_rx_cb);
          `uvm_info(`gtn, $sformatf("rx parity bit %0b", cfg.vif.uart_rx), UVM_DEBUG)
          item.parity = cfg.vif.uart_rx;
          if (cfg.en_rx_checks && item.parity != `GET_PARITY(item.data, cfg.odd_parity)) begin
            `uvm_error(`gtn, "Parity failed")
          end
        end
        else item.parity = 1'b0;

        // get the stop bit
        @(cfg.vif.mon_rx_mp.mon_rx_cb);
        `uvm_info(`gtn, $sformatf("rx stop bit %0b", cfg.vif.uart_rx), UVM_DEBUG)
        item.stop_bit = cfg.vif.uart_rx;
        // check stop bit
        if (cfg.en_rx_checks && cfg.vif.uart_rx !== 1'b1) begin
          `uvm_error(`gtn, "No stop bit when expected!")
        end
        `uvm_info(`gtn, $sformatf("collected uart rx txn:\n%0s", item.sprint()), UVM_HIGH)
        rx_analysis_port.write(item);

        // wait for uart_rx_clk_pulses==0, otherwise, it may affect next transaction
        cfg.vif.wait_for_rx_idle();

        if (cfg.en_cov) cov.uart_cg.sample(UartRx, item);
        process_objections(UartRx, 0);
      end else begin
        @(cfg.vif.uart_rx);
      end
    end
  endtask

  task drive_tx_clk();
    forever begin
      if (cfg.vif.uart_tx_clk_pulses > 0) begin
        #(cfg.vif.uart_clk_period_ns / 2);
        cfg.vif.uart_tx_clk = ~cfg.vif.uart_tx_clk;
        #(cfg.vif.uart_clk_period_ns / 2);
        cfg.vif.uart_tx_clk = ~cfg.vif.uart_tx_clk;
        cfg.vif.uart_tx_clk_pulses--;
      end else begin
        @(cfg.vif.uart_tx, cfg.vif.uart_tx_clk_pulses);
      end
    end
  endtask

  task drive_rx_clk();
    forever begin
      if (cfg.vif.uart_rx_clk_pulses > 0) begin
        #(cfg.vif.uart_clk_period_ns / 2);
        cfg.vif.uart_rx_clk = ~cfg.vif.uart_rx_clk;
        #(cfg.vif.uart_clk_period_ns / 2);
        cfg.vif.uart_rx_clk = ~cfg.vif.uart_rx_clk;
        cfg.vif.uart_rx_clk_pulses--;
      end else begin
        @(cfg.vif.uart_rx, cfg.vif.uart_rx_clk_pulses);
      end
    end
  endtask

  virtual task process_reset();
    if (cfg.en_cov) begin
      cov.uart_reset_cg.sample(UartTx, cfg.vif.uart_tx_clk_pulses);
      cov.uart_reset_cg.sample(UartRx, cfg.vif.uart_rx_clk_pulses);
    end
    cfg.vif.uart_tx_clk_pulses = 0;
    cfg.vif.uart_tx_clk        = 1;
    cfg.vif.uart_rx_clk_pulses = 0;
    cfg.vif.uart_rx_clk        = 1;
    process_objections(UartTx, 0);
    process_objections(UartRx, 0);
    wait(!cfg.under_reset);
  endtask

  virtual function void process_objections(uart_dir_e dir, bit raise);
    if (raise && !obj_raised[dir]) begin
      `uvm_info(`gfn, $sformatf("raising objection for %0s", dir.name), UVM_HIGH)
      m_current_phase.raise_objection(this);
      obj_raised[dir] = 1'b1;
    end
    else if (!raise && obj_raised[dir]) begin
      `uvm_info(`gfn, $sformatf("dropping objection for %0s", dir.name), UVM_HIGH)
      m_current_phase.drop_objection(this);
      obj_raised[dir] = 1'b0;
    end
  endfunction
endclass
