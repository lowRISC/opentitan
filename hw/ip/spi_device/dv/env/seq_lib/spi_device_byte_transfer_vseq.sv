// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Byte Access test to verify proper byte data transfer without timeout expiring
class spi_device_byte_transfer_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_byte_transfer_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans == 20;
  }

  virtual task body();
    bit [39:0] host_data;
    bit [31:0] device_data;
    bit [7:0]  device_data_exp[$] = {1,2,3,4,5};
    uint       avail_bytes;
    uint       avail_data;
    bit [2:0]  bits_num;

    spi_device_init();
    ral.cfg.timer_v.set(8'hFF);
    csr_update(.csr(ral.cfg));

    for (int i = 1; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      repeat ($urandom_range(2, 10)) begin
        bit [31:0] host_data_exp_q[$];
        `DV_CHECK_STD_RANDOMIZE_FATAL(host_data)
        `DV_CHECK_STD_RANDOMIZE_FATAL(device_data)
        // check if tx sram full and wait for at least a word to become available
        //wait_for_tx_avail_bytes(SRAM_WORD_SIZE, SramSpaceAvail, avail_bytes);
        write_device_words_to_send({device_data});
        `uvm_info(`gfn, $sformatf("Device Data = 0x%0h", device_data), UVM_LOW)
        cfg.clk_rst_vif.wait_clks(16);
        //wait_for_tx_filled_rx_space_bytes(SRAM_WORD_SIZE, avail_bytes);
        cfg.m_spi_agent_cfg.partial_byte = 1;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bits_num, bits_num > 0;)
        cfg.m_spi_agent_cfg.bits_to_transfer = bits_num;
        `uvm_info(`gfn, $sformatf("Bits_num = 0x%0h", bits_num), UVM_LOW)
        spi_host_xfer_byte(host_data[7:0], device_data_exp[0]);
        `uvm_info(`gfn, $sformatf("new device data 0 = 0x%0h", device_data_exp[0]), UVM_LOW)
        cfg.clk_rst_vif.wait_clks(4);
        //read_rx_avail_bytes(SramDataAvail, avail_data);
        //`DV_CHECK_CASE_EQ(avail_data, 0)
        cfg.m_spi_agent_cfg.partial_byte = 0;
        cfg.m_spi_agent_cfg.bits_to_transfer = 8;
        spi_host_xfer_byte(host_data[15:8], device_data_exp[1]);
        `uvm_info(`gfn, $sformatf("new device data 1 = 0x%0h", device_data_exp[1]), UVM_LOW)
        spi_host_xfer_byte(host_data[23:16], device_data_exp[2]);
        `uvm_info(`gfn, $sformatf("new device data 2 = 0x%0h", device_data_exp[2]), UVM_LOW)
        spi_host_xfer_byte(host_data[31:24], device_data_exp[3]);
        `uvm_info(`gfn, $sformatf("new device data 3 = 0x%0h", device_data_exp[3]), UVM_LOW)
        //cfg.m_spi_agent_cfg.partial_byte = 1;
        //cfg.m_spi_agent_cfg.bits_to_transfer = 5;
        spi_host_xfer_byte(host_data[39:32], device_data_exp[4]);
        `uvm_info(`gfn, $sformatf("new device data 4 = 0x%0h", device_data_exp[4]), UVM_LOW)
        // check if rx sram is empty and wait for at least a word to arrive
        //wait_for_rx_avail_bytes(SRAM_WORD_SIZE, SramDataAvail, avail_bytes);
        //read_host_words_rcvd(1, host_data_exp_q);
        //`DV_CHECK_CASE_EQ(host_data[39:8], host_data_exp_q[0])
        `DV_CHECK_CASE_EQ(device_data,
            {device_data_exp[4],device_data_exp[3], device_data_exp[2], device_data_exp[1]})
        //check_for_tx_rx_idle();
      end
    end
  endtask : body

endclass : spi_device_byte_transfer_vseq
