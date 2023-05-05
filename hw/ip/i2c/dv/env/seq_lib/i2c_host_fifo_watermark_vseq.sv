// Copyright lowRISC contributors.
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
  // set write transaction size to fmt_fifo depth is enough to cross the highest fmtilvl value
  constraint num_wr_bytes_c { num_wr_bytes == I2C_FMT_FIFO_DEPTH; }
  // read transaction length is equal to rx_fifo depth to cross rxilvl
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
            // depending the programmed fmtivl and the DUT configuration
            // (timing regsisters), cnt_fmt_threshold could be
            //   1: fmtilvl is crossed one   when data drains from fmt_fifo
            //   2: fmtilvl is crossed twice when data fills up or drains from fmt_fifo
            if (!cfg.under_reset) begin
              `DV_CHECK_GT(cnt_fmt_threshold, 0)
              `DV_CHECK_LE(cnt_fmt_threshold, 2)
              `uvm_info(`gfn, $sformatf("\n cnt_fmt_threshold %0d", cnt_fmt_threshold), UVM_DEBUG)
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
            // for fmtilvl > 4, rx_threshold is disabled (cnt_rx_threshold = 0)
            // otherwise, cnt_rx_threshold must be 1
            if (!cfg.under_reset) begin
              if ( rxilvl <= 4) begin
                `DV_CHECK_EQ(cnt_rx_threshold, 1)
              end else begin
                `DV_CHECK_EQ(cnt_rx_threshold, 0)
              end
              // during a read transaction, fmt_threshold could be triggered since read address
              // and control byte are programmed to fmt_fifo and possibly cross fmtilvl
              // if fmt_threshold is triggered, then it should be cleared to not interfere
              // counting fmt_threshold in the next transaction (no need to verify
              // fmt_threshold again during read)
              `uvm_info(`gfn, $sformatf("\n cnt_rx_threshold %0d", cnt_rx_threshold), UVM_DEBUG)
            end
            clear_interrupt(FmtThreshold);
          end
        end
        begin
          while (!cfg.under_reset && check_fmt_threshold) process_fmt_threshold_intr();
        end
        begin
          while (!cfg.under_reset && check_rx_threshold) process_rx_threshold_intr();
        end
      join
    end
    `uvm_info(`gfn, "\n--> end of i2c_host_fifo_watermark_vseq", UVM_DEBUG)
  endtask : body

  task process_fmt_threshold_intr();
    bit fmt_threshold;
    bit [TL_DW-1:0] fmt_lvl, fmt_ilvl, intr_enable;

    @(posedge cfg.clk_rst_vif.clk);
    csr_rd(.ptr(ral.intr_enable), .value(intr_enable), .backdoor(1'b1));
    if (intr_enable[FmtThreshold] && cfg.intr_vif.pins[FmtThreshold]) begin
      cnt_fmt_threshold++;
      // read registers
      csr_rd(.ptr(ral.fifo_ctrl.fmtilvl), .value(fmt_ilvl));
      csr_rd(.ptr(ral.fifo_status.fmtlvl), .value(fmt_lvl));
      `uvm_info(`gfn, $sformatf("\n fmtilvl %0d, fmtlvl %0d", fmt_ilvl, fmt_lvl), UVM_DEBUG)
      // bound checking for fmt_lvl w.r.t fmt_ilvl because rx_fifo can received an extra data
      // before fmt_threshold intr pin is asserted (corner case)
      if (!cfg.under_reset) begin
        case (fmt_ilvl)
          0: bound_check(fmt_lvl, 1, 2);
          1: bound_check(fmt_lvl, 4, 5);
          2: bound_check(fmt_lvl, 8, 9);
          default: bound_check(fmt_lvl, 16, 17);
        endcase
      end
      clear_interrupt(FmtThreshold);
    end
  endtask : process_fmt_threshold_intr

  task process_rx_threshold_intr();
    bit rx_threshold;
    bit [TL_DW-1:0] rx_lvl, rx_ilvl, intr_enable;

    @(posedge cfg.clk_rst_vif.clk);
    csr_rd(.ptr(ral.intr_enable), .value(intr_enable), .backdoor(1'b1));
    if (intr_enable[RxThreshold] && cfg.intr_vif.pins[RxThreshold]) begin
      cnt_rx_threshold++;
      // read registers
      csr_rd(.ptr(ral.fifo_status.rxlvl), .value(rx_lvl));
      csr_rd(.ptr(ral.fifo_ctrl.rxilvl), .value(rx_ilvl));
      // bound checking for rx_lvl w.r.t rx_ilvl because rx_fifo can received an extra data
      // before rx_threshold intr pin is asserted (corner case)
      if (!cfg.under_reset) begin
        case (rx_ilvl)
          0: bound_check(rx_lvl, 1, 2);
          1: bound_check(rx_lvl, 4, 5);
          2: bound_check(rx_lvl, 8, 9);
          3: bound_check(rx_lvl, 16, 17);
          4: bound_check(rx_lvl, 30, 31);
          default: `uvm_error(`gfn, "\n Invalid rx_ilvl")
        endcase
      end
      clear_interrupt(RxThreshold);
    end
  endtask : process_rx_threshold_intr

endclass : i2c_host_fifo_watermark_vseq
