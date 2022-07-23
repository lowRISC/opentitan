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
    // Only SPI mode 0 is supported (CPHA=0, CPOL=0).
    cfg.spi_host_agent_cfg.sck_polarity[0] = 0;
    cfg.spi_host_agent_cfg.sck_phase[0] = 0;
    // Only support tx/rx_order = 0
    cfg.spi_host_agent_cfg.host_bit_dir = 0;
    cfg.spi_host_agent_cfg.device_bit_dir = 0;
    ral.cfg.tx_order.set(cfg.spi_host_agent_cfg.host_bit_dir);
    ral.cfg.rx_order.set(cfg.spi_host_agent_cfg.device_bit_dir);
    ral.cfg.cpol.set(1'b0);
    ral.cfg.cpha.set(1'b0);
    csr_update(.csr(ral.cfg));

    ral.tpm_cfg.en.set(1'b1);
    // 1 for CRB, 0 for FIFO.

    csr_update(.csr(ral.tpm_cfg));

    //Csb select for TPM
    cfg.spi_host_agent_cfg.csb_sel = 1;

  endtask : tpm_init

  // Randomise other fields in TPM_CFG.
  virtual task tpm_configure();
    ral.tpm_cfg.tpm_mode.set(TpmCrbMode); // TODO randomize for locality test
    ral.tpm_cfg.hw_reg_dis.set(1); // TODO randomize for locality test
    ral.tpm_cfg.tpm_reg_chk_dis.set(1); // TODO randomize for locality test
    ral.tpm_cfg.invalid_locality.set(0); // TODO randomize for locality test
    csr_update(.csr(ral.tpm_cfg));
    `uvm_info(`gfn, ral.tpm_cfg.sprint(), UVM_MEDIUM)
  endtask : tpm_configure

  // Randomise other fields in TPM_CFG.
  virtual task tpm_configure_locality();
    ral.tpm_cfg.tpm_mode.set(TpmFifoMode); // FIFO Mode
    ral.tpm_cfg.hw_reg_dis.set(0);
    ral.tpm_cfg.tpm_reg_chk_dis.set(0);
    ral.tpm_cfg.invalid_locality.set(1);
    csr_update(.csr(ral.tpm_cfg));
    `uvm_info(`gfn, ral.tpm_cfg.sprint(), UVM_MEDIUM)
  endtask : tpm_configure_locality

  // Check the CMD_ADDR/wrFIFO contents.
  virtual task check_tpm_cmd_addr(bit [7:0] exp_cmd, bit [23:0] exp_addr);
    bit [31:0] cmd_addr_data;
    bit [7:0] act_cmd;
    bit [23:0] act_addr;

    // first sent byte is MSB of the address
    exp_addr = {exp_addr[7:0], exp_addr[15:8], exp_addr[23:16]};
    // Check command and address fifo
    csr_rd(.ptr(ral.tpm_cmd_addr), .value(cmd_addr_data));
    act_cmd = get_field_val(ral.tpm_cmd_addr.cmd, cmd_addr_data);
    act_addr = get_field_val(ral.tpm_cmd_addr.addr, cmd_addr_data);
    `DV_CHECK_CASE_EQ(act_cmd, exp_cmd)
    `DV_CHECK_CASE_EQ(act_addr, exp_addr)
  endtask : check_tpm_cmd_addr

  // Check the CMD_ADDR/wrFIFO contents.
  virtual task check_tpm_write_fifo(byte data_bytes[$]);
    bit [7:0]  wrfifo_data;

    // Check write fifo
    for (int i = 1; i <= 4; i++) begin
      csr_rd(.ptr(ral.tpm_write_fifo), .value(wrfifo_data));
      `uvm_info(`gfn, $sformatf("WR FIFO Content = 0x%0h", wrfifo_data), UVM_LOW)
      `DV_CHECK_CASE_EQ(wrfifo_data, data_bytes[i])
    end
  endtask : check_tpm_write_fifo

  // Poll for START symbol from TPM, collect device data
  virtual task poll_start_collect_data(byte data_bytes[5], ref bit [7:0] returned_bytes[*]);
    int pay_num = 0;
    bit [7:0]  device_byte_rsp;
    `DV_SPINWAIT(
      while (pay_num < 5) begin
        spi_host_xfer_byte(data_bytes[pay_num], device_byte_rsp);
        `uvm_info(`gfn, $sformatf("Device Resp = 0x%0h", device_byte_rsp), UVM_LOW)
        if (pay_num > 0) begin
          returned_bytes[pay_num - 1] = device_byte_rsp;
          pay_num++;
        end
        if ((pay_num == 0  && device_byte_rsp == TPM_START)) pay_num++;
        if (pay_num == 4) cfg.spi_host_agent_cfg.csb_consecutive = 0;
      end
    )
  endtask : poll_start_collect_data

endclass : spi_device_tpm_base_vseq
