// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


class uart_monitor extends dv_base_monitor#(
    .ITEM_T (uart_item),
    .CFG_T  (uart_agent_cfg),
    .COV_T  (uart_agent_cov)
  );
  `uvm_component_utils(uart_monitor)

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
        mon_tx_stable();
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
        item = uart_item::type_id::create("item");
        // get the start bit
        @(cfg.vif.mon_tx_mp.mon_tx_cb);
        `uvm_info(`gfn, $sformatf("tx start bit %0b", cfg.vif.uart_tx), UVM_DEBUG)
        item.start_bit = cfg.vif.uart_tx;
        // get the data bits
        for (int i = 0; i < 8; i++) begin
          @(cfg.vif.mon_tx_mp.mon_tx_cb);
          `uvm_info(`gfn, $sformatf("tx data bit[%0d] %0b", i, cfg.vif.uart_tx), UVM_DEBUG)
          item.data[i] = cfg.vif.uart_tx;
        end
        // get the parity bit
        if (cfg.vif.uart_tx_clk_pulses > 2) begin
          @(cfg.vif.mon_tx_mp.mon_tx_cb);
          `uvm_info(`gfn, $sformatf("tx parity bit %0b", cfg.vif.uart_tx), UVM_DEBUG)
          item.parity = cfg.vif.uart_tx;
          if (cfg.en_tx_checks && item.parity != `GET_PARITY(item.data, cfg.odd_parity)) begin
            `uvm_error(`gfn, "Parity failed")
          end
        end
        else item.parity = 1'b0;

        // get the stop bit
        @(cfg.vif.mon_tx_mp.mon_tx_cb);
        `uvm_info(`gfn, $sformatf("tx stop bit %0b", cfg.vif.uart_tx), UVM_DEBUG)
        item.stop_bit = cfg.vif.uart_tx;
        // check stop bit
        if (cfg.en_tx_checks && cfg.vif.uart_tx !== 1'b1) begin
          `uvm_error(`gfn, "No stop bit when expected!")
        end
        `uvm_info(`gfn, $sformatf("collected uart tx txn:\n%0s", item.sprint()), UVM_HIGH)
        tx_analysis_port.write(item);

        // wait for uart_tx_clk_pulses==0, otherwise, it may affect next transaction
        cfg.vif.wait_for_tx_idle();

        if (cfg.en_cov) cov.uart_cg.sample(UartTx, item);
      end else begin
        @(cfg.vif.uart_tx);
      end
    end
  endtask

  virtual task collect_rx_data();
    uart_item item;
    forever begin
      if (cfg.vif.uart_rx === 1'b0 && cfg.en_rx_monitor == 1) begin
        item = uart_item::type_id::create("item");
        cfg.vif.uart_rx_clk_pulses = NUM_UART_XFER_BITS_WO_PARITY + cfg.en_parity;
        // get the start bit
        @(cfg.vif.mon_rx_mp.mon_rx_cb);
        `uvm_info(`gfn, $sformatf("rx start bit %0b", cfg.vif.uart_rx), UVM_DEBUG)
        item.start_bit = cfg.vif.uart_rx;
        // get the data bits
        for (int i = 0; i < 8; i++) begin
          @(cfg.vif.mon_rx_mp.mon_rx_cb);
          `uvm_info(`gfn, $sformatf("rx data bit[%0d] %0b", i, cfg.vif.uart_rx), UVM_DEBUG)
          item.data[i] = cfg.vif.uart_rx;
        end
        // get the parity bit
        if (cfg.vif.uart_rx_clk_pulses > 2) begin
          @(cfg.vif.mon_rx_mp.mon_rx_cb);
          `uvm_info(`gfn, $sformatf("rx parity bit %0b", cfg.vif.uart_rx), UVM_DEBUG)
          item.parity = cfg.vif.uart_rx;
          if (cfg.en_rx_checks && item.parity != `GET_PARITY(item.data, cfg.odd_parity)) begin
            `uvm_error(`gfn, "Parity failed")
          end
        end
        else item.parity = 1'b0;

        // get the stop bit
        @(cfg.vif.mon_rx_mp.mon_rx_cb);
        `uvm_info(`gfn, $sformatf("rx stop bit %0b", cfg.vif.uart_rx), UVM_DEBUG)
        item.stop_bit = cfg.vif.uart_rx;
        // check stop bit
        if (cfg.en_rx_checks && cfg.vif.uart_rx !== 1'b1) begin
          `uvm_error(`gfn, "No stop bit when expected!")
        end
        `uvm_info(`gfn, $sformatf("collected uart rx txn:\n%0s", item.sprint()), UVM_HIGH)
        rx_analysis_port.write(item);

        // wait for uart_rx_clk_pulses==0, otherwise, it may affect next transaction
        cfg.vif.wait_for_rx_idle();

        if (cfg.en_cov) cov.uart_cg.sample(UartRx, item);
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
        // last cycle only use half period as design and agent aren't using same clock. If agent
        // freq is slower and design continues sending tx item, the freq diff will be accumulated.
        // Ending current item after latch STOP bit to allow agent to re-establish clock to sample
        // the START bit of next item
        if (cfg.vif.uart_tx_clk_pulses == 1) #(cfg.vif.uart_clk_period_ns / 4);
        else                                 #(cfg.vif.uart_clk_period_ns / 2);
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

  // actual uart clock isn't ideal, it's allowed to off less than max_drift_cycle_pct cycle as cfg
  // this to check data stable from (50 - max_drift_cycle_pct) to (50 + max_drift_cycle_pct)
  task mon_tx_stable();
    forever begin
      @(cfg.vif.uart_tx_clk_pulses);
      if (cfg.vif.uart_tx_clk_pulses == 0) continue;

      #(cfg.vif.uart_clk_period_ns * (50 - cfg.get_max_drift_cycle_pct()) / 100);
      `DV_SPINWAIT_EXIT(
          begin
            @(cfg.vif.uart_tx);
            `uvm_error(`gfn, $sformatf(
                "Expect uart_tx stable from %0d to %0d of the period, but it's changed",
                50 - cfg.get_max_drift_cycle_pct(), 50 + cfg.get_max_drift_cycle_pct()))
          end,
          // simplified from cfg.vif.uart_clk_period_ns * max_drift_cycle_pct * 2 / 100
          #(cfg.vif.uart_clk_period_ns * cfg.get_max_drift_cycle_pct() / 50))
    end
  endtask

  // update ok_to_end to prevent sim finish when there is any activity on the bus
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.uart_tx_clk_pulses or cfg.vif.uart_rx_clk_pulses);
      ok_to_end = (cfg.vif.uart_tx_clk_pulses == 0) && (cfg.vif.uart_rx_clk_pulses == 0);
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
    wait(!cfg.under_reset);
  endtask

endclass
