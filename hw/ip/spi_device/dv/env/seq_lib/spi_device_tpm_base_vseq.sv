// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Task library for TPM related operations
class spi_device_tpm_base_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_tpm_base_vseq)
  `uvm_object_new

  bit             tpm_cfg_en;
  tpm_cfg_mode_e  tpm_cfg_mode;
  rand bit        tpm_cfg_hw_reg_dis;
  rand bit        tpm_cfg_reg_chk_dis;
  rand bit        tpm_cfg_inv_locality;
  rand bit [23:0] tpm_address;

  // Constrain within the range of TPM HW regs to be used in locality tests
  constraint tpm_address_c {
    tpm_address inside {[24'hD4_00_00:24'hD4_FF_FF]};
  }

  // Configure clocks and tpm, generate a word.
  virtual task tpm_init();
    cfg.m_spi_agent_cfg.sck_polarity[0] = 0;
    cfg.m_spi_agent_cfg.sck_phase[0] = 0;
    cfg.m_spi_agent_cfg.host_bit_dir = 1;
    cfg.m_spi_agent_cfg.device_bit_dir = 1;
    ral.cfg.tx_order.set(1);
    ral.cfg.rx_order.set(1);
    ral.cfg.cpol.set(1'b0);
    ral.cfg.cpha.set(1'b0);
    csr_update(.csr(ral.cfg)); // TODO check if randomization possible

    ral.tpm_cfg.en.set(1'b1);
    // 1 for CRB, 0 for FIFO.

    csr_update(.csr(ral.tpm_cfg));

    //Csb select for TPM
    cfg.m_spi_agent_cfg.csb_sel = 1;

  endtask : tpm_init

  // Randomise other fields in TPM_CFG.
  virtual task tpm_configure();
    ral.tpm_cfg.tpm_mode.set(1'b1); // TODO randomize for locality test
    ral.tpm_cfg.hw_reg_dis.set(1); // TODO randomize for locality test
    ral.tpm_cfg.tpm_reg_chk_dis.set(1); // TODO randomize for locality test
    ral.tpm_cfg.invalid_locality.set(0); // TODO randomize for locality test
    csr_update(.csr(ral.tpm_cfg));
    `uvm_info(`gfn, ral.tpm_cfg.sprint(), UVM_MEDIUM)
  endtask : tpm_configure

  // Check the CMD_ADDR/wrFIFO contents.
  virtual task chk_fifo_contents(bit [31:0] addr_cmd, byte data_bytes[$]);
    bit [7:0]  wrfifo_data;
    bit [31:0] chk_cmd_addr_data;

    // Check command and address fifo
    csr_rd(.ptr(ral.tpm_cmd_addr), .value(chk_cmd_addr_data));
    addr_cmd = {<<1{addr_cmd}};
    `DV_CHECK_CASE_EQ(addr_cmd, chk_cmd_addr_data)

    // Check write fifo
    for (int i = 1; i <= 4; i++) begin
      csr_rd(.ptr(ral.tpm_write_fifo), .value(wrfifo_data));
      `uvm_info(`gfn, $sformatf("WR FIFO Content = 0x%0h", wrfifo_data), UVM_LOW)
      data_bytes[i] = {<<1{data_bytes[i]}};
      `DV_CHECK_CASE_EQ(wrfifo_data, data_bytes[i])
    end

  endtask : chk_fifo_contents

endclass : spi_device_tpm_base_vseq
