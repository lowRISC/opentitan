// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Bit Access test to verify proper handling of partial byte transfers
class spi_device_bit_transfer_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_bit_transfer_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans == 20;
  }

  virtual task body();
    bit [39:0] host_data;
    bit [31:0] device_data;
    bit [7:0]  device_data_exp[$] = {1,2,3,4,5}; // Init
    uint       avail_bytes;
    uint       avail_data;
    bit [2:0]  bits_num;

    for (int i = 1; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      spi_device_init();
      repeat ($urandom_range(8)) begin
        bit [31:0] host_data_exp_q[$];
        `DV_CHECK_STD_RANDOMIZE_FATAL(host_data)
        `DV_CHECK_STD_RANDOMIZE_FATAL(device_data)
        write_device_words_to_send({device_data});
        `uvm_info(`gfn, $sformatf("Device Data = 0x%0h", device_data), UVM_LOW)
        cfg.clk_rst_vif.wait_clks(16);
        cfg.spi_host_agent_cfg.partial_byte = 1;
        // Randomize number of bits to send before CSN deassert
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bits_num, bits_num > 0;)
        cfg.spi_host_agent_cfg.bits_to_transfer = bits_num;
        `uvm_info(`gfn, $sformatf("Bits_num = 0x%0h", bits_num), UVM_LOW)
        spi_host_xfer_byte(host_data[7:0], device_data_exp[0]);
        `uvm_info(`gfn, $sformatf("new device data 0 = 0x%0h", device_data_exp[0]), UVM_LOW)
        cfg.clk_rst_vif.wait_clks(4);
        cfg.spi_host_agent_cfg.partial_byte = 0;
        spi_host_xfer_byte(host_data[15:8], device_data_exp[1]);
        `uvm_info(`gfn, $sformatf("new device data 1 = 0x%0h", device_data_exp[1]), UVM_LOW)
        spi_host_xfer_byte(host_data[23:16], device_data_exp[2]);
        `uvm_info(`gfn, $sformatf("new device data 2 = 0x%0h", device_data_exp[2]), UVM_LOW)
        spi_host_xfer_byte(host_data[31:24], device_data_exp[3]);
        `uvm_info(`gfn, $sformatf("new device data 3 = 0x%0h", device_data_exp[3]), UVM_LOW)
        // In case of 7 bits, first 7 bits will not be repeated
        if (bits_num < 7) begin
          spi_host_xfer_byte(host_data[39:32], device_data_exp[4]);
          `uvm_info(`gfn, $sformatf("new device data 4 = 0x%0h", device_data_exp[4]), UVM_LOW)
        end
        if (bits_num < 7) begin
          `DV_CHECK_CASE_EQ(device_data,
              {device_data_exp[4],device_data_exp[3], device_data_exp[2], device_data_exp[1]})
        end else begin
          if (cfg.spi_host_agent_cfg.device_bit_dir == 1)  begin
            device_data[7] = 0;
          end else begin
            device_data[0] = 0;
          end
          `DV_CHECK_CASE_EQ(device_data,
              {device_data_exp[3],device_data_exp[2], device_data_exp[1], device_data_exp[0]})
        end
      end
    end
  endtask : body

endclass : spi_device_bit_transfer_vseq
