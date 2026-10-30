// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// passthrough_mode test vseq
// SPI_HOST HWIP Technical Specification Block Diagram
class spi_host_passthrough_mode_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_passthrough_mode_vseq)
  `uvm_object_new

  virtual task pre_start();
    cfg.en_scb = 0;
    super.pre_start();
  endtask

  // If set and NumCS > 1, the host core holds CSB[held_csid] active during the test, so that the
  // checks see whether passthrough keeps the other CSB lines inactive.
  rand bit hold_csb;
  rand int unsigned held_csid;

  constraint hold_csb_c {
    SPI_HOST_NUM_CS == 1 -> hold_csb == 1'b0;
    hold_csb dist {1'b1 := 3, 1'b0 := 1};
  }

  constraint held_csid_c {
    SPI_HOST_NUM_CS > 1 -> held_csid inside {[1:SPI_HOST_NUM_CS-1]};
    SPI_HOST_NUM_CS == 1 -> held_csid == 0;
  }

  // Issue a dummy-cycle command on CSB[held_csid] and keep that line active (csaat = 1) or release
  // it (csaat = 0).
  virtual task hold_core_csb(bit csaat);
    spi_host_command_t cmd;
    cmd.direction = None;
    cmd.mode      = Standard;
    cmd.csaat     = csaat;
    cmd.len       = 0;
    program_command_reg(cmd);
    // Wait until the command has completed.  With csaat, CSB[held_csid] then stays active.
    `DV_WAIT(cfg.spi_passthrough_vif.cio_csb_o[held_csid] === !csaat,
             $sformatf("CSB[%0d] did not become %0d", held_csid, !csaat),
             cfg.csr_spinwait_timeout_ns)
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0));
  endtask

  virtual task body();
    bit en = 1'b1;
    bit output_en;
    // The CSB lines that the host core drives while passthrough is disabled
    bit [SPI_HOST_NUM_CS-1:0] core_csb = '1;

    // CONTROL.OUTPUT_EN controls the output enables of the CSB lines other than CSB[0] in
    // passthrough mode and of all lines outside passthrough mode.
    `DV_CHECK_STD_RANDOMIZE_FATAL(output_en)
    ral.control.output_en.set(output_en);
    if (hold_csb) begin
      ral.control.spien.set(1'b1);
    end
    csr_update(ral.control);

    if (hold_csb) begin
      `uvm_info(`gfn, $sformatf("Holding CSB[%0d] active during passthrough", held_csid), UVM_LOW)
      csr_wr(.ptr(ral.csid), .value(held_csid));
      hold_core_csb(.csaat(1'b1));
      core_csb[held_csid] = 1'b0;
    end

    fork
    begin
      forever begin
        if(!en) break;
        @(posedge cfg.clk_rst_vif.clk);
        if (cfg.spi_passthrough_vif.passthrough_en) begin
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_o, cfg.spi_passthrough_vif.sck)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_en_o, cfg.spi_passthrough_vif.sck_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_o[0], cfg.spi_passthrough_vif.csb)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_en_o[0], cfg.spi_passthrough_vif.csb_en)
          // Passthrough uses CSB[0] only; the other CSB lines are inactive.
          for (int i = 1; i < SPI_HOST_NUM_CS; i++) begin
            `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_o[i], 1'b1)
            `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_en_o[i], output_en)
          end
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, cfg.spi_passthrough_vif.s_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_o, cfg.spi_passthrough_vif.is)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_i, cfg.spi_passthrough_vif.os)
        end else begin
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_o, 1'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_en_o, output_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_o, core_csb)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_en_o, {SPI_HOST_NUM_CS{output_en}})
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, 4'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_o, 4'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.os, 4'hf)
        end
      end
    end
    begin
      while (en) begin
        @(posedge cfg.clk_rst_vif.clk);
        cfg.spi_passthrough_vif.sck_en <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.csb_en <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.s_en   <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.csb    <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.sck    <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.is     <= $urandom_range(100, 2000);
        cfg.spi_passthrough_vif.cio_sd_i <= $urandom_range(100, 2000);
      end
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 20));
    end
    begin
      @(posedge cfg.clk_rst_vif.clk);
      for (int i = 0; i < (num_trans*num_runs); i++) begin
        @(posedge cfg.clk_rst_vif.clk);
        // Enable passthrough in the first iteration and disable it in the second one, so that
        // both modes are checked even if there are only a few iterations.
        case (i)
          0:       cfg.spi_passthrough_vif.passthrough_en <= 1'b1;
          1:       cfg.spi_passthrough_vif.passthrough_en <= 1'b0;
          default: cfg.spi_passthrough_vif.passthrough_en <= $urandom_range(0, 1);
        endcase
        cfg.clk_rst_vif.wait_clks($urandom_range(100, 200));
      end
      en = 1'b0;
    end
    join

    if (hold_csb) begin
      // Release CSB[held_csid] so that the agent sees all CSB lines inactive at the end.
      cfg.spi_passthrough_vif.passthrough_en <= 1'b0;
      hold_core_csb(.csaat(1'b0));
    end
  endtask : body
endclass : spi_host_passthrough_mode_vseq
