// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test the watermark interrupt of fmt_fifo and rx_fifo
// TODO: Weicai's comments in PR #3128: consider constraining rx_fifo_access_dly
// to test watermark irq
class i2c_fifo_watermark_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_fifo_watermark_vseq)
  `uvm_object_new

  // fast write data to fmt_fifo to quickly trigger fmt_watermark interrupt
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}

  // fast read data from rd_fifo after crossing watermark level to quickly finish simulation
  constraint rx_fifo_access_dly_c { rx_fifo_access_dly == 0;}

  // write transaction length is more than fmt_fifo depth to cross fmtilvl
  constraint num_wr_bytes_c {
    solve num_data_ovf before num_wr_bytes;
    num_wr_bytes == I2C_FMT_FIFO_DEPTH + num_data_ovf;
  }
  // read transaction length is equal to rx_fifo depth to cross rxilvl
  constraint num_rd_bytes_c { num_rd_bytes == I2C_RX_FIFO_DEPTH; }

  // counting the number of received watermark interrupts
  local uint cnt_fmt_watermark;
  local uint cnt_rx_watermark;

  virtual task pre_start();
    super.pre_start();
    // config rx_watermark test (fmt_watermark test is auto configured)
    cfg.seq_cfg.en_rx_watermark = 1'b1;
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
    bit check_fmt_watermark, check_rx_watermark;

    initialization();
    `uvm_info(`gfn, "\n--> start of i2c_fifo_watermark_vseq", UVM_DEBUG)
    for (int i = 1; i <= num_trans; i++) begin
      check_fmt_watermark = 1'b1;
      check_rx_watermark  = 1'b1;
      cnt_fmt_watermark   = 0;
      cnt_rx_watermark    = 0;
      `uvm_info(`gfn, $sformatf("\n  run simulation %0d/%0d", i, num_trans), UVM_DEBUG)
      fork
        begin
          //*** verify fmt_watermark irq:
          // -> send write transaction -> pooling and counting fmt_watermark interrupt
          // -> check write complete -> stop pooling fmt_watermark interrupt
          // -> verify the number of received fmt_watermark interrupt
          if (check_fmt_watermark) begin
            host_send_trans(1, WriteOnly);
            check_fmt_watermark = 1'b0;  // gracefully stop process_fmt_watermark_intr
            // depending the programmed fmtivl and the DUT configuration
            // (timing regsisters), cnt_fmt_watermark could be
            //   1: fmtilvl is crossed one   when data drains from fmt_fifo
            //   2: fmtilvl is crossed twice when data fills up or drains from fmt_fifo
            if (!cfg.under_reset) begin
              `DV_CHECK_GT(cnt_fmt_watermark, 0)
              `DV_CHECK_LE(cnt_fmt_watermark, 2)
              `uvm_info(`gfn, $sformatf("\n cnt_fmt_watermark %0d", cnt_fmt_watermark), UVM_DEBUG)
            end
          end

          //*** verify rx_watermark irq:
          // -> send read transaction -> pooling and counting rx_watermark interrupt
          // -> check read complete -> stop pooling rx_watermark interrupt
          // -> verify the number of received rx_watermark interrupt
          if (check_rx_watermark) begin
            // first en_rx_watermark is unset to quickly fill up rx_fifo and
            // watermark interrupt is assuredly triggered
            // until rx_fifo becomes full, en_rx_watermark is set to start reading rx_fifo
            host_send_trans(1, ReadOnly);
            check_rx_watermark = 1'b0; // gracefully stop process_rx_watermark_intr
            // for fmtilvl > 4, rx_watermark is disable (cnt_rx_watermark = 0)
            // otherwise, cnt_rx_watermark must be 1
            if (!cfg.under_reset) begin
              if ( rxilvl <= 4) begin
                `DV_CHECK_EQ(cnt_rx_watermark, 1)
              end else begin
                `DV_CHECK_EQ(cnt_rx_watermark, 0)
              end
              // during a read transaction, fmt_watermark could be triggered since read address
              // and control byte are programmed to fmt_fifo and possibly cross fmtilvl
              // if fmt_watermark is triggered, then it should be cleared to not interfere
              // counting fmt_watermark in the next transaction (no need to verify
              // fmt_watermark again during read)
              `uvm_info(`gfn, $sformatf("\n cnt_rx_watermark %0d", cnt_rx_watermark), UVM_DEBUG)
            end
            clear_interrupt(FmtWatermark);
          end
        end
        begin
          while (!cfg.under_reset && check_fmt_watermark) process_fmt_watermark_intr();
        end
        begin
          while (!cfg.under_reset && check_rx_watermark) process_rx_watermark_intr();
        end
      join
    end
    `uvm_info(`gfn, "\n--> end of i2c_fifo_watermark_vseq", UVM_DEBUG)
  endtask : body

  task process_fmt_watermark_intr();
    bit fmt_watermark;
    bit [TL_DW-1:0] fmt_lvl, fmt_ilvl, intr_enable;

    @(posedge cfg.clk_rst_vif.clk);
    csr_rd(.ptr(ral.intr_enable), .value(intr_enable), .backdoor(1'b1));
    if (intr_enable[FmtWatermark] && cfg.intr_vif.pins[FmtWatermark]) begin
      cnt_fmt_watermark++;
      // read registers via backdoor
      csr_rd(.ptr(ral.fifo_ctrl.fmtilvl), .value(fmt_ilvl), .backdoor(1'b1));
      csr_rd(.ptr(ral.fifo_status.fmtlvl), .value(fmt_lvl), .backdoor(1'b1));
      `uvm_info(`gfn, $sformatf("\n fmtilvl %0d, fmtlvl %0d", fmt_ilvl, fmt_lvl), UVM_LOW)
      // bound checking for fmt_lvl w.r.t fmt_ilvl because rx_fifo can received an extra data
      // before fmt_watermark intr pin is asserted (corner case)
      if (!cfg.under_reset) begin
        case (fmt_ilvl)
          0: bound_check(fmt_lvl, 1, 2);
          1: bound_check(fmt_lvl, 4, 5);
          2: bound_check(fmt_lvl, 8, 9);
          default: bound_check(fmt_lvl, 16, 17);
        endcase
      end
      clear_interrupt(FmtWatermark);
    end
  endtask : process_fmt_watermark_intr

  task process_rx_watermark_intr();
    bit rx_watermark;
    bit [TL_DW-1:0] rx_lvl, rx_ilvl, intr_enable;

    @(posedge cfg.clk_rst_vif.clk);
    csr_rd(.ptr(ral.intr_enable), .value(intr_enable), .backdoor(1'b1));
    if (intr_enable[RxWatermark] && cfg.intr_vif.pins[RxWatermark]) begin
      cnt_rx_watermark++;
      // read registers via backdoor
      csr_rd(.ptr(ral.fifo_status.rxlvl), .value(rx_lvl), .backdoor(1'b1));
      csr_rd(.ptr(ral.fifo_ctrl.rxilvl), .value(rx_ilvl), .backdoor(1'b1));
      // bound checking for rx_lvl w.r.t rx_ilvl because rx_fifo can received an extra data
      // before rx_watermark intr pin is asserted (corner case)
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
      clear_interrupt(RxWatermark);
    end
  endtask : process_rx_watermark_intr
  
endclass : i2c_fifo_watermark_vseq

