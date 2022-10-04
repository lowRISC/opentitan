// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Task library for TPM related operations
class spi_device_tpm_base_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_tpm_base_vseq)
  `uvm_object_new

  // tpm_addr constraint knobs
  rand bit        is_hw_reg_offset; // offset matches to one of the hw_reg
  rand bit        is_hw_reg_region; // is at region 'hD4_xxxx
  rand bit        is_valid_locality;

  rand bit [TPM_ADDR_WIDTH-1:0] tpm_addr;

  constraint tpm_addr_c {
    solve is_hw_reg_offset, is_hw_reg_region, is_valid_locality before tpm_addr;

    is_hw_reg_offset -> tpm_addr[TPM_OFFSET_WIDTH-1:0] inside {ALL_TPM_HW_REG_OFFSETS};
    is_hw_reg_region -> tpm_addr inside {[24'hD4_0000:24'hD4_FFFF]};
    is_valid_locality ->
      tpm_addr[TPM_OFFSET_WIDTH+TPM_LOCALITY_WIDTH-1:TPM_OFFSET_WIDTH] < MAX_TPM_LOCALITY;
  }

  rand uint tpm_size;

  constraint tpm_size_c {
    tpm_size dist {
      [1:3]              :/ 1,
      4                  :/ 2,
      [5:MAX_SUPPORT_TPM_SIZE-1] :/ 2,
      MAX_SUPPORT_TPM_SIZE       :/ 1
    };
  }

  rand uint tpm_write;

  // randomize all the TPM transaction related fields - addr, write, size.
  virtual function void randomize_tpm_trans();
    `DV_CHECK(this.randomize(is_hw_reg_offset, is_hw_reg_region, is_valid_locality, tpm_addr,
                             tpm_size, tpm_write))
  endfunction
  // Configure clocks and tpm, generate a word.
  virtual task tpm_init(tpm_cfg_mode_e mode, bit is_hw_return = $random);
    cfg.spi_host_agent_cfg.csid = TPM_CSB_ID;
    // Only SPI mode 0 is supported (CPHA=0, CPOL=0).
    cfg.spi_host_agent_cfg.sck_polarity[TPM_CSB_ID] = 0;
    cfg.spi_host_agent_cfg.sck_phase[TPM_CSB_ID] = 0;
    // Only support tx/rx_order = 0
    cfg.spi_host_agent_cfg.host_bit_dir = 0;
    cfg.spi_host_agent_cfg.device_bit_dir = 0;
    ral.cfg.tx_order.set(cfg.spi_host_agent_cfg.host_bit_dir);
    ral.cfg.rx_order.set(cfg.spi_host_agent_cfg.device_bit_dir);
    ral.cfg.cpol.set(1'b0);
    ral.cfg.cpha.set(1'b0);
    csr_update(.csr(ral.cfg));

    ral.tpm_cfg.en.set(1'b1);
    ral.tpm_cfg.tpm_mode.set(mode);
    if (is_hw_return) begin
      ral.tpm_cfg.hw_reg_dis.set(0);
      ral.tpm_cfg.invalid_locality.set(1);
    end else begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.tpm_cfg.hw_reg_dis)
      `DV_CHECK_RANDOMIZE_FATAL(ral.tpm_cfg.invalid_locality)
    end
    `DV_CHECK_RANDOMIZE_FATAL(ral.tpm_cfg.tpm_reg_chk_dis)
    csr_update(.csr(ral.tpm_cfg));
    `uvm_info(`gfn, ral.tpm_cfg.sprint(), UVM_MEDIUM)
  endtask : tpm_init

  // Check the CMD_ADDR/wrFIFO contents.
  virtual task wait_and_check_tpm_cmd_addr(bit [7:0] exp_cmd, bit [23:0] exp_addr);
    bit [31:0] cmd_addr_data;
    bit [7:0] act_cmd;
    bit [23:0] act_addr;

    csr_spinwait(.ptr(ral.intr_state.tpm_header_not_empty), .exp_data(1));
    // Check command and address fifo
    csr_rd(.ptr(ral.tpm_cmd_addr), .value(cmd_addr_data));
    act_cmd = get_field_val(ral.tpm_cmd_addr.cmd, cmd_addr_data);
    act_addr = get_field_val(ral.tpm_cmd_addr.addr, cmd_addr_data);
    `DV_CHECK_CASE_EQ(act_cmd, exp_cmd)
    `DV_CHECK_CASE_EQ(act_addr, exp_addr)

    // clear the interrupt
    csr_wr(ral.intr_state.tpm_header_not_empty, 1);
  endtask : wait_and_check_tpm_cmd_addr

  virtual task wait_and_process_tpm_fifo(bit write,
                                         bit [TPM_ADDR_WIDTH-1:0] exp_addr,
                                         uint exp_num_bytes,
                                         output bit [7:0] byte_q[$]);
    wait_and_check_tpm_cmd_addr(get_tpm_cmd(write, exp_num_bytes), exp_addr);
    // Upon receiving read command, set read fifo contents
    if (write) begin
      bit [7:0] wrfifo_byte;
      for (int i; i < exp_num_bytes;) begin
        // wait until fifo size > 0
        csr_spinwait(.ptr(ral.tpm_status.wrfifo_depth), .exp_data(0), .compare_op(CompareOpGt));
        `DV_CHECK_LE(i + `gmv(ral.tpm_status.wrfifo_depth), exp_num_bytes)

        repeat (`gmv(ral.tpm_status.wrfifo_depth)) begin
          csr_rd(.ptr(ral.tpm_write_fifo), .value(wrfifo_byte));
          `uvm_info(`gfn, $sformatf("TPM Write FIFO Content = 0x%0h", wrfifo_byte), UVM_MEDIUM)
          byte_q.push_back(wrfifo_byte);
          i++;
        end
      end
    end else begin
      bit [31:0] word_q[$];
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(byte_q, byte_q.size() == exp_num_bytes;)
      byte_q_to_word_q(byte_q, word_q);
      foreach (word_q[i]) csr_wr(.ptr(ral.tpm_read_fifo), .value(word_q[i]));
    end
  endtask : wait_and_process_tpm_fifo

  virtual task spi_host_xfer_tpm_item(input bit write,
                                      input uint tpm_size = 0,
                                      input bit [TPM_ADDR_WIDTH-1:0] addr,
                                      output bit [7:0] payload_q[$]);
    spi_host_tpm_seq m_host_tpm_seq;

    `uvm_create_on(m_host_tpm_seq, p_sequencer.spi_sequencer_h)
    m_host_tpm_seq.csb_sel = TPM_CSB_ID;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_host_tpm_seq,
                                   write_command == write;
                                   addr == local::addr;
                                   if (write) {
                                     data_q.size() == tpm_size;
                                   } else {
                                    read_size == tpm_size;
                                   })
    `uvm_send(m_host_tpm_seq)
    payload_q = m_host_tpm_seq.rsp.data;
  endtask
endclass : spi_device_tpm_base_vseq
