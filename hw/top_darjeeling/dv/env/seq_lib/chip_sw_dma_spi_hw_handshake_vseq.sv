// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_dma_spi_hw_handshake_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_dma_spi_hw_handshake_vseq)

  `uvm_object_new

  localparam string DMA_FSM_STATE_PATH =
    "tb.dut.top_darjeeling.u_dma.ctrl_state_q";

  task pre_start();
    // Setting the byte order to 0 ensures that the 4 byte transaction sent to
    // the agent from the DUT is played back in exactly the same order, thus
    // making things easy to compare.
    cfg.m_spi_device_agent_cfgs[0].byte_order = '0;
    super.pre_start();
  endtask

  virtual task cpu_init();
    super.cpu_init();
  endtask

  virtual task body();
    spi_device_dma_seq m_device_dma_seq;
    bit [31:0] exp_digest[16];
    bit[7:0] sha_mode_arr[1];
    bit [7:0] kSoftwareBarrier[] = '{0};
    bit abort = 1'b0;
    int retval;
    bit [$bits(dma_pkg::dma_ctrl_state_e)-1:0] dma_state;
    time dma_busy_timeout = 120_000_000; // 120ms

    spi_device_dma_seq::data_t msg;

    super.body();
    `uvm_info(`gfn, "Testing with spi host 0", UVM_LOW)

    void'($value$plusargs("abort=%0d", abort));

    if (abort) begin
      `uvm_info(`gfn, "Testing abort mode", UVM_LOW)
    end else begin
      `uvm_info(`gfn, "Testing normal DMA transfer", UVM_LOW)
    end

    // enable spi agent
    cfg.chip_vif.enable_spi_device(.inst_num(0), .enable(1));

    // Wait for the sw to finish configuring the spi_host DUT
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "spi host configuration complete",
             "Timedout waiting for spi host c configuration.")

    // create and start the spi_device sequence
    m_device_dma_seq = spi_device_dma_seq::type_id::create("m_device_dma_seq");
    msg = m_device_dma_seq.get_data();

    // Randomize the SHA mode and compute the expected hash of the source data
    unique case($urandom_range(0, 2))
      0: begin
        cryptoc_dpi_pkg::sv_dpi_get_sha256_digest(msg, exp_digest[0:7]);
        sha_mode_arr = {dma_pkg::OpcSha256};
      end
      1: begin
        cryptoc_dpi_pkg::sv_dpi_get_sha384_digest(msg, exp_digest[0:11]);
        sha_mode_arr = {dma_pkg::OpcSha384};
      end
      2: begin
        cryptoc_dpi_pkg::sv_dpi_get_sha512_digest(msg, exp_digest[0:15]);
        sha_mode_arr = {dma_pkg::OpcSha512};
      end
      default: begin
        `dv_fatal("Invalid SHA mode.")
      end
    endcase

    // By default, the hardware outputs little-endian data for each digest (32 bits). But DPI
    // functions expect output to be big-endian.
    for (int i = 0; i < 16; ++i) begin
      exp_digest[i] = {<<8{exp_digest[i]}};
    end

    // Backdoor the software with the SHA mode and the expected digest
    sw_symbol_backdoor_overwrite("kShaMode", sha_mode_arr);
    sw_symbol_backdoor_overwrite("kShaDigestExpData", {<<8{{<<32{exp_digest}}}});

    fork
      begin
        m_device_dma_seq.start(p_sequencer.spi_device_sequencer_hs[0]);
      end
      begin
        if (abort) begin
          // Wait until the DMA performs the first transfer
          `DV_SPINWAIT(while (dma_state != dma_pkg::DmaWaitReadResponse) begin
                  retval = uvm_hdl_read(DMA_FSM_STATE_PATH, dma_state);
                  `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", DMA_FSM_STATE_PATH))
                  cfg.clk_rst_vif.wait_clks(1);
                end,
                "timeout while wait for test exit complete",
                dma_busy_timeout)
          // Wait a random delay
          cfg.clk_rst_vif.wait_clks($urandom_range(1, 10000));

          // Backdoor the SW to perform the abort
          kSoftwareBarrier[0] = 1;
          `uvm_info(`gfn, $sformatf("Setting kSoftwareBarrier = %0d", 1), UVM_LOW)
          sw_symbol_backdoor_overwrite("kSoftwareBarrier", kSoftwareBarrier);

          // Stop the running sequence
          p_sequencer.spi_device_sequencer_hs[0].stop_sequences();

          // Wait for the sw to finish configuring the spi_host DUT
          `DV_WAIT(cfg.sw_logger_vif.printed_log == "spi host re-configuration complete",
             "Timedout waiting for spi host c configuration.")

          // Restart the SPI sequence
          m_device_dma_seq.start(p_sequencer.spi_device_sequencer_hs[0]);
        end
      end
    join_none
  endtask
endclass : chip_sw_dma_spi_hw_handshake_vseq
