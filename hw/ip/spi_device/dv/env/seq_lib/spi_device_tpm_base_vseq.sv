// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_tpm_base_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_tpm_base_vseq)
  `uvm_object_new

  bit             tpm_cfg_en;
  rand bit        tpm_cfg_mode;
  rand bit        tpm_cfg_hw_reg_dis;
  rand bit        tpm_cfg_reg_chk_dis;
  bit             tpm_cfg_inv_locality;
  rand bit [23:0] tpm_addr;
  bit      [31:0] tpm_host_word;
  rand bit [31:0] tpm_host_payload;
  rand bit [31:0] tpm_device_word;
  bit      [31:0] device_resp;
  bit      [4:0]  tpm_chk_stat;
  string          mode;

  // Constrain within the range of TPM HW regs.
  constraint tpm_host_word_c {
    tpm_addr inside {[24'hD4_00_00:24'hD4_FF_FF]};
  }

  // Configure clocks and tpm, generate a word.
  virtual task tpm_init();
    bit host_bit_dir = 1'b1;
    ral.cfg.cpol.set(1'b0);
    ral.cfg.cpha.set(1'b0);
    cfg.m_spi_agent_cfg.sck_polarity = 0;
    cfg.m_spi_agent_cfg.sck_phase = 0;
    csr_update(.csr(ral.cfg));

    ral.tpm_cfg.en.set(1'b1);
    // 1 for CRB, 0 for FIFO.
    ral.tpm_cfg.tpm_mode.set(1'b1); //tpm_cfg_mode);
    cfg.m_spi_agent_cfg.host_bit_dir = host_bit_dir;
    ral.cfg.rx_order.set(host_bit_dir);
    csr_update(.csr(ral.tpm_cfg));

    cfg.m_spi_agent_cfg.csb_sel = 1;
    mode = (tpm_cfg_mode) ? "CRB" : "FIFO";
    `uvm_info(`gfn, $sformatf("%s", mode), UVM_LOW)

  endtask : tpm_init

  // Randomise other fields in TPM_CFG.
  virtual task tpm_configure();
    ral.tpm_cfg.hw_reg_dis.set(tpm_cfg_hw_reg_dis);
    ral.tpm_cfg.tpm_reg_chk_dis.set(tpm_cfg_reg_chk_dis);
    ral.tpm_cfg.invalid_locality.set(tpm_cfg_inv_locality);
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

  endtask : chk_cmd_addr

  // Check TPM_STATUS.cmdaddr_notempty, INTR_STATE.tpm_header_notempty and
  // interrupt status information.
  virtual task chk_tpm_status(bit [4:0] tpm_current_status);
    bit cmdaddr_notempty_bit;
    bit intf_capa_bit;
    bit int_enable_bit;
    bit int_vector_bit;
    bit int_stat_bit;

    csr_rd(.ptr(ral.tpm_status.cmdaddr_notempty), .value(cmdaddr_notempty_bit));
    csr_rd(.ptr(ral.tpm_intf_capability), .value(intf_capa_bit));
    csr_rd(.ptr(ral.tpm_int_enable), .value(int_enable_bit));
    csr_rd(.ptr(ral.tpm_int_vector), .value(int_vector_bit));
    csr_rd(.ptr(ral.tpm_int_status), .value(int_stat_bit));

    tpm_current_status = {cmdaddr_notempty_bit, intf_capa_bit, int_enable_bit, int_vector_bit, int_stat_bit};

    `uvm_info(`gfn, $sformatf("(dut) cmdaddr_notempty: %b", cmdaddr_notempty_bit), UVM_LOW)
    `uvm_info(`gfn, $sformatf("(dut) intf_capability: %b", intf_capa_bit), UVM_LOW)
    `uvm_info(`gfn, $sformatf("(dut) int_enable: %b", int_enable_bit), UVM_LOW)
    `uvm_info(`gfn, $sformatf("(dut) int_vector: %b", int_vector_bit), UVM_LOW)
    `uvm_info(`gfn, $sformatf("(dut) int_stat: %b", int_stat_bit), UVM_LOW)

    `uvm_info(`gfn, ral.tpm_cfg.sprint(), UVM_LOW)
  endtask : chk_tpm_status

endclass : spi_device_tpm_base_vseq