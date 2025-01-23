// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_spi_device_tpm_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_spi_device_tpm_vseq)

  `uvm_object_new

  rand bit [23:0] addr;
  rand bit [7:0] data_q[$];
  constraint size_c  { data_q.size() <= 64 && data_q.size > 0; }

  virtual task tpm_txn (bit wr, bit [23:0] addr, bit [7:0] data_q[$] = {0},
                        int len, output logic [7:0] rdata_q[]);
    spi_host_tpm_seq m_host_tpm_seq;
    `uvm_create_on(m_host_tpm_seq, p_sequencer.spi_host_sequencer_h)

    // Common attribute assignments
    m_host_tpm_seq.write_command = wr;
    m_host_tpm_seq.addr = addr;

    // This is a write transaction
    if (wr) begin
      m_host_tpm_seq.data_q = data_q;
    end else begin
      m_host_tpm_seq.read_size = len;
    end

    `uvm_send(m_host_tpm_seq)
    `uvm_info(`gfn, $sformatf("TPM transaction sent"), UVM_MEDIUM)

    // This is a read trasnaction
    if (!wr) begin
      rdata_q = m_host_tpm_seq.rsp.data;
    end
  endtask

  virtual task body();
    logic [7:0] rdata_q[];
    super.body();

    // Enable desired modes
    cfg.chip_vif.enable_spi_host = 0;
    cfg.chip_vif.enable_spi_tpm = 1;

    // Directly set the expected cs_id
    cfg.m_spi_host_agent_cfg.csb_sel_in_cfg = 1;
    cfg.m_spi_host_agent_cfg.csid = 1;

    // enable spi agent interface to begin
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Begin TPM Test",
             "Timedout waiting for spi host c configuration.")

    for (int i = 0; i < 10; i++) begin
      `uvm_info(`gfn, $sformatf("Begin transaction %d", i), UVM_MEDIUM)

      // Write transaction
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(data_q)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(addr)
      foreach (data_q[i]) begin
        `uvm_info(`gfn, $sformatf("Expected data: 0x%x", data_q[i]), UVM_MEDIUM)
      end
      tpm_txn (.wr(1), .addr(addr), .data_q(data_q), .len(data_q.size()), .rdata_q(rdata_q));

      // Read transaction
      tpm_txn (.wr(0), .addr(addr), .len(data_q.size()), .rdata_q(rdata_q));
      foreach (rdata_q[i]) begin
        `uvm_info(`gfn, $sformatf("Read data: 0x%x", data_q[i]), UVM_MEDIUM)
      end

      // Confirm that data is looped back
      `DV_CHECK_Q_EQ(data_q, rdata_q);
      `uvm_info(`gfn, $sformatf("End transaction %d", i), UVM_MEDIUM)
    end
  endtask


endclass : chip_sw_spi_device_tpm_vseq
