// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test the threshold interrupt of fmt_fifo and rx_fifo
class i2c_host_fifo_watermark_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_fifo_watermark_vseq)
  `uvm_object_new

  // fast write data to fmt_fifo to quickly trigger fmt_threshold interrupt
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}
  // fast read data from rd_fifo after crossing threshold level to quickly finish simulation
  constraint rx_fifo_access_dly_c { rx_fifo_access_dly == 0;}
  // set write transaction size to fmt_fifo depth is enough to cross most fmt_thresh values
  constraint num_wr_bytes_c { num_wr_bytes == I2C_FMT_FIFO_DEPTH; }
  // read transaction length is equal to rx_fifo depth to cross rx_thresh
  constraint num_rd_bytes_c { num_rd_bytes == I2C_RX_FIFO_DEPTH; }

  // counting the number of received threshold interrupts
  local uint cnt_fmt_threshold;
  local uint cnt_rx_threshold;

  virtual task pre_start();
    super.pre_start();
    // config rx_threshold test (fmt_threshold test is configured by default)
    cfg.seq_cfg.en_rx_threshold = 1'b1;
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
    bit check_fmt_threshold, check_rx_threshold;

    initialization();
    `uvm_info(`gfn, "\n--> start of i2c_host_fifo_watermark_vseq", UVM_DEBUG)
    for (int i = 1; i <= num_trans; i++) begin
      check_fmt_threshold = 1'b1;
      check_rx_threshold  = 1'b1;
      cnt_fmt_threshold   = 0;
      cnt_rx_threshold    = 0;
      `uvm_info(`gfn, $sformatf("\n  run simulation %0d/%0d", i, num_trans), UVM_DEBUG)
      fork
        begin
          //*** verify fmt_threshold irq:
          // -> send write transaction -> pooling and counting fmt_threshold interrupt
          // -> check write complete -> stop pooling fmt_threshold interrupt
          // -> verify the number of received fmt_threshold interrupt
          if (check_fmt_threshold) begin
            host_send_trans(.max_trans(1), .trans_type(WriteOnly));
            check_fmt_threshold = 1'b0;  // gracefully stop process_fmt_threshold_intr
            // cnt_fmt_threshold could be asserted 0 to 3 times:
            // - 0 if a threshold of 0 is chosen, below which the FMT depth never falls
            // - 1 if the FMT depth falls below the threshold once and stays there
            // - 2 if the FMT depth starts below the threshold, raises above, and falls below again
            // - 3 if the FMT depth briefly drops below the threshold once it has raised above,
            //   which happens when the FSM pops an item from the FIFO after the FMT depth has
            //   raised above the threshold and before the vseq pushes the next item
            if (!cfg.under_reset) begin
              `uvm_info(`gfn, $sformatf("\n cnt_fmt_threshold %0d", cnt_fmt_threshold), UVM_DEBUG)
              `DV_CHECK_GE(cnt_fmt_threshold, 0)
              `DV_CHECK_LE(cnt_fmt_threshold, 3)
            end
          end

          //*** verify rx_threshold irq:
          // -> send read transaction -> pooling and counting rx_threshold interrupt
          // -> check read complete -> stop pooling rx_threshold interrupt
          // -> verify the number of received rx_threshold interrupt
          if (check_rx_threshold) begin
            // first en_rx_threshold is unset to quickly fill up rx_fifo and
            // threshold interrupt is assuredly triggered
            // until rx_fifo becomes full, en_rx_threshold is set to start reading rx_fifo
            host_send_trans(.max_trans(1), .trans_type(ReadOnly));
            check_rx_threshold = 1'b0; // gracefully stop process_rx_threshold_intr
            if (!cfg.under_reset) begin
              // The number of rx_threshold interrupts depends only on whether filling the RX FIFO
              // exceeded the threshold; 1 if so, otherwise 0.
              bit [TL_DW-1:0] rx_thresh;
              csr_rd(.ptr(ral.host_fifo_config.rx_thresh), .value(rx_thresh));
              `DV_CHECK_EQ(cnt_rx_threshold, rx_thresh < I2C_RX_FIFO_DEPTH);
              // during a read transaction, fmt_threshold could be triggered since read address
              // and control byte are programmed to fmt_fifo and possibly cross fmt_thresh
              // if fmt_threshold is triggered, then it should be cleared to not interfere
              // counting fmt_threshold in the next transaction (no need to verify
              // fmt_threshold again during read)
              `uvm_info(`gfn, $sformatf("\n cnt_rx_threshold %0d", cnt_rx_threshold), UVM_DEBUG)
            end
          end
        end
        begin
          // Count any rising edges on the fmt_threshold interrupt line
          bit was_asserted = cfg.intr_vif.pins[FmtThreshold];
          while (!cfg.under_reset && check_fmt_threshold) process_fmt_threshold_intr(was_asserted);
        end
        begin
          // Count any rising edges on the rx_threshold interrupt line
          bit was_asserted = cfg.intr_vif.pins[RxThreshold];
          while (!cfg.under_reset && check_rx_threshold) process_rx_threshold_intr(was_asserted);
        end
      join
    end
    `uvm_info(`gfn, "\n--> end of i2c_host_fifo_watermark_vseq", UVM_DEBUG)
  endtask : body

  task process_fmt_threshold_intr(ref bit was_asserted);
    bit [TL_DW-1:0] fmt_lvl, fmt_thresh;

    @(posedge cfg.clk_rst_vif.clk);
    if (cfg.intr_vif.pins[FmtThreshold]) begin
      if (!was_asserted) begin
        cnt_fmt_threshold++;
        // read registers
        csr_rd(.ptr(ral.host_fifo_config.fmt_thresh), .value(fmt_thresh));
        csr_rd(.ptr(ral.host_fifo_status.fmtlvl), .value(fmt_lvl));
        `uvm_info(`gfn, $sformatf("\n fmt_thresh %0d, fmtlvl %0d", fmt_thresh, fmt_lvl), UVM_DEBUG)
        if (!cfg.under_reset) begin
          // TODO: Decide on the bounds here; FIFO could have been drained somewhat by the point
          // at which we manage to read the CSR (randomized delays).
          bound_check(fmt_lvl, 0, fmt_thresh);
        end
      end
      was_asserted = 1'b1;
    end else was_asserted = 1'b0;
  endtask : process_fmt_threshold_intr

  task process_rx_threshold_intr(ref bit was_asserted);
    bit [TL_DW-1:0] rx_lvl, rx_thresh;

    @(posedge cfg.clk_rst_vif.clk);
    if (cfg.intr_vif.pins[RxThreshold]) begin
      if (!was_asserted) begin
        cnt_rx_threshold++;
        // read registers
        csr_rd(.ptr(ral.host_fifo_status.rxlvl), .value(rx_lvl));
        csr_rd(.ptr(ral.host_fifo_config.rx_thresh), .value(rx_thresh));
        // bound checking for rx_lvl w.r.t rx_thresh because rx_fifo can receive an extra datum
        // before rx_threshold intr pin is asserted (corner case)
        `uvm_info(`gfn, $sformatf("\n rx_thresh %0d, rx_lvl %0d", rx_thresh, rx_lvl), UVM_DEBUG)
        if (!cfg.under_reset) begin
          bound_check(rx_lvl, rx_thresh, rx_thresh + 1);
        end
      end
      was_asserted = 1'b1;
    end else was_asserted = 1'b0;
  endtask : process_rx_threshold_intr

endclass : i2c_host_fifo_watermark_vseq
