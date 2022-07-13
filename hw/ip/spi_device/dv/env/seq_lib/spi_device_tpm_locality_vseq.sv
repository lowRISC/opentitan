// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Locality test, making transactions of various locality
// Targeting HW sts register, randomizing it and checking data returned to host
class spi_device_tpm_locality_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_locality_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  device_byte_rsp;
    bit [7:0]  tpm_cmd = TPM_READ_CMD; //TPM Read command
    bit [23:0] tpm_addr;
    bit [31:0] address_command;
    byte data_bytes[$];
    bit [7:0] returned_bytes[*];
    int pay_num;
    bit [31:0]  wrfifo_data;
    bit [7:0] access_q[$];
    bit [31:0] sts;
    bit [3:0] locality;
    bit [11:0] hw_address;

    spi_device_init();

    // randomised tpm configuration.
    tpm_init();
    tpm_configure_locality();
    repeat (num_trans) begin
      pay_num = 0;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(access_q, access_q.size() == 5;)
      `DV_CHECK_STD_RANDOMIZE_FATAL(sts)
      ral.tpm_access_0.set({access_q[3], access_q[2], access_q[1], access_q[0]});
      csr_update(.csr(ral.tpm_access_0));
      ral.tpm_access_1.set(access_q[4]);
      csr_update(.csr(ral.tpm_access_1));
      ral.tpm_sts.sts.set(sts);
      csr_update(.csr(ral.tpm_sts));
      cfg.clk_rst_vif.wait_clks(100);
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(locality, locality <= 4;)
      // Data size will be 5, first byte dummy for polling, remaining 4 for payload
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_bytes, data_bytes.size() == 5;)
      tpm_addr = get_tpm_addr(locality);
      tpm_addr = {<<1{tpm_addr}};
      address_command = {tpm_addr, tpm_cmd};
      `uvm_info(`gfn, $sformatf("Address Command = 0x%0h", address_command), UVM_LOW)
      // send payload
      cfg.spi_host_agent_cfg.csb_consecutive = 1;
      spi_host_xfer_word(address_command, device_word_rsp);
      // poll START and collect data
      poll_start_collect_data(data_bytes, returned_bytes);

      if (access_q[locality][5] == 1) begin
        `DV_CHECK_CASE_EQ({returned_bytes[3], returned_bytes[2], returned_bytes[1],
                          returned_bytes[0]}, sts)
      end else begin
        `DV_CHECK_CASE_EQ({returned_bytes[3], returned_bytes[2], returned_bytes[1],
                          returned_bytes[0]}, 32'hFFFFFFFF)
      end

      cfg.clk_rst_vif.wait_clks(100);
    end

  endtask : body

endclass : spi_device_tpm_locality_vseq
