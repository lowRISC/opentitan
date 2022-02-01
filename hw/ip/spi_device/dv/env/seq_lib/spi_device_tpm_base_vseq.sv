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
  virtual task chk_fifo_contents(bit [31:0] addr_cmd, byte data_bytes[$]);
    bit [7:0]  wrfifo_data;
    bit [31:0] chk_cmd_addr_data;

    // Check command and address fifo
    csr_rd(.ptr(ral.tpm_cmd_addr), .value(chk_cmd_addr_data));

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

  // Poll for START symbol from TPM, collect device data
  virtual task poll_start_collect_data(byte data_bytes[5], ref bit [7:0] returned_bytes[*]);
    int pay_num = 0;
    bit [7:0]  device_byte_rsp;
    while (pay_num < 5) begin
      spi_host_xfer_byte(data_bytes[pay_num], device_byte_rsp);
      device_byte_rsp = {<<1{device_byte_rsp}};
      `uvm_info(`gfn, $sformatf("Device Resp = 0x%0h", device_byte_rsp), UVM_LOW)
      if (pay_num > 0) begin
        returned_bytes[pay_num - 1] = device_byte_rsp;
        pay_num++;
      end
      if ((pay_num == 0  && device_byte_rsp == TPM_START)) pay_num++;
      if (pay_num == 4) cfg.m_spi_agent_cfg.csb_consecutive = 0;
    end
  endtask : poll_start_collect_data

  virtual task tpm_read_trans(bit [7:0] tpm_cmd);
    bit [31:0] device_word_rsp;
    bit [23:0] read_tpm_addr;
    bit [23:0] tpm_addr_read;
    bit [31:0] read_address_command;
    byte data_bytes[$];
    bit [7:0] returned_bytes[*];
    bit [7:0] read_fifo_data[$];

    // send cmd_addr
    `DV_CHECK_STD_RANDOMIZE_FATAL(read_tpm_addr)

    // Data size will be 5, first byte dummy for polling, remaining 4 for payload
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_bytes, data_bytes.size() == 5;)

    read_tpm_addr = {<<1{read_tpm_addr}};
    read_address_command = {read_tpm_addr, tpm_cmd};
    `uvm_info(`gfn, $sformatf("Address Command = 0x%0h", read_address_command), UVM_LOW)
    cfg.m_spi_agent_cfg.csb_consecutive = 1;
    spi_host_xfer_word(read_address_command, device_word_rsp);
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
  endtask : tpm_read_trans

  virtual task tpm_write_trans(bit [7:0] tpm_cmd);
    bit [31:0] device_word_rsp;
    bit [7:0]  device_byte_rsp;
    bit [23:0] write_tpm_addr;
    bit [31:0] write_address_command;
    byte data_bytes[$];
    int pay_num;

    // send cmd_addr
    `DV_CHECK_STD_RANDOMIZE_FATAL(write_tpm_addr)

    // Data size will be 5, first byte dummy for polling, remaining 4 for payload
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_bytes, data_bytes.size() == 5;)

    write_address_command = {write_tpm_addr, tpm_cmd};
    `uvm_info(`gfn, $sformatf("Address Command = 0x%0h", write_address_command), UVM_LOW)

    // send payload
    cfg.m_spi_agent_cfg.csb_consecutive = 1;
    spi_host_xfer_word(write_address_command, device_word_rsp);
    while (pay_num < 5) begin
      spi_host_xfer_byte(data_bytes[pay_num], device_byte_rsp);
      `uvm_info(`gfn, $sformatf("Device Resp = 0x%0h", device_byte_rsp), UVM_LOW)
      device_byte_rsp = {<<1{device_byte_rsp}};
      if (pay_num > 0) pay_num++;
      if (pay_num == 0  && device_byte_rsp == TPM_START) pay_num++;
      if (pay_num == 4) cfg.m_spi_agent_cfg.csb_consecutive = 0;
    end
    cfg.clk_rst_vif.wait_clks(10);
    chk_fifo_contents(write_address_command, data_bytes);
    write_tpm_addr = 0;

  endtask : tpm_write_trans

endclass : spi_device_tpm_base_vseq
