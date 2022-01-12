// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Read test, issuing READ command, writing to read fifo, checking host received data
class spi_device_tpm_read_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_read_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  device_byte_rsp;
    bit [7:0]  tpm_cmd = TPM_READ_CMD; //TPM Read command
    bit [23:0] tpm_addr;
    bit [23:0] tpm_addr_read;
    bit [31:0] address_command;
    byte data_bytes[$];
    bit [7:0] returned_bytes[*];
    int pay_num;
    bit [31:0]  wrfifo_data;
    bit [7:0] read_fifo_data[$];
    bit [3:0] locality;
    bit [11:0] hw_address;

    spi_device_init();

    // randomised tpm configuration.
    tpm_init();
    tpm_configure();
    repeat (num_trans) begin
      pay_num = 0;

      cfg.clk_rst_vif.wait_clks(100);
      // send cmd_addr
      `DV_CHECK_STD_RANDOMIZE_FATAL(tpm_addr)
      // Data size will be 5, first byte dummy for polling, remaining 4 for payload
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_bytes, data_bytes.size() == 5;)
      tpm_addr = {<<1{tpm_addr}};
      address_command = {tpm_addr, tpm_cmd};
      `uvm_info(`gfn, $sformatf("Address Command = 0x%0h", address_command), UVM_LOW)
      cfg.m_spi_agent_cfg.csb_consecutive = 1;
      spi_host_xfer_word(address_command, device_word_rsp);
      fork
        begin
          csr_rd(.ptr(ral.tpm_cmd_addr), .value(tpm_addr_read));
          // Upon receiving read command, set read fifo contents
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(read_fifo_data, read_fifo_data.size() == 4;)
          foreach (read_fifo_data[i]) csr_wr(.ptr(ral.tpm_read_fifo), .value(read_fifo_data[i]));
        end // Write Read Fifo Thread
        begin
          // poll START and collect data
          poll_start_collect_data(data_bytes, returned_bytes);
        end // Poll read data thread
      join

      `DV_CHECK_CASE_EQ({returned_bytes[3], returned_bytes[2], returned_bytes[1],
                          returned_bytes[0]}, {read_fifo_data[3], read_fifo_data[2],
                          read_fifo_data[1], read_fifo_data[0]})

      cfg.clk_rst_vif.wait_clks(100);
    end

  endtask : body

endclass : spi_device_tpm_read_vseq
