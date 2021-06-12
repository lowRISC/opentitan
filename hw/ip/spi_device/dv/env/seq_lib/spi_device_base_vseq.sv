// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_base_vseq extends cip_base_vseq #(
        .CFG_T               (spi_device_env_cfg),
        .RAL_T               (spi_device_reg_block),
        .COV_T               (spi_device_env_cov),
        .VIRTUAL_SEQUENCER_T (spi_device_virtual_sequencer)
    );
  `uvm_object_utils(spi_device_base_vseq)

  bit do_spi_device_init    = 1'b0;
  bit do_spi_device_mem_cfg = 1'b1;

  bit [1:0] spi_mode = 0; // TODO fixed value in spec now

  rand bit sck_polarity;
  rand bit sck_phase;
  rand bit host_bit_dir;
  rand bit device_bit_dir;

  rand uint sram_host_base_addr;
  rand uint sram_host_limit_addr;
  rand uint sram_device_base_addr;
  rand uint sram_device_limit_addr;
  // helper variables
  rand uint num_host_sram_words;
  rand uint num_device_sram_words;
  rand uint sram_host_byte_size;
  rand uint sram_device_byte_size;

  rand bit [15:0] tx_watermark_lvl;
  rand bit [15:0] rx_watermark_lvl;

  // core clk freq / spi clk freq is from 1/4 to 8. use below 2 var to represent the ratio
  // if spi_freq_faster,  core_spi_freq_ratio = spi clk freq / core clk freq (1:4)
  // if !spi_freq_faster, core_spi_freq_ratio = core clk freq / spi clk freq (1:8)
  rand uint core_spi_freq_ratio;
  rand bit  spi_freq_faster;

  // override it in random seq
  constraint sram_addr_c {
    // host and device addr space within sram should not overlap
    sram_host_base_addr == 32'h0;
    sram_host_limit_addr == 32'h1ff; // 512 bytes
    sram_device_base_addr == 32'h200;
    sram_device_limit_addr == 32'h3ff; // 512 bytes
  }

  constraint sram_size_c {
    solve num_host_sram_words before sram_host_byte_size;
    solve num_device_sram_words before sram_device_byte_size;
    num_host_sram_words   == sram_host_limit_addr[31:2] - sram_host_base_addr[31:2] + 1;
    num_device_sram_words == sram_device_limit_addr[31:2] - sram_device_base_addr[31:2] + 1;
    sram_host_byte_size   == num_host_sram_words << 2;
    sram_device_byte_size == num_device_sram_words << 2;
  }

  constraint tx_watermark_lvl_c {
    tx_watermark_lvl dist {
      [0 : SRAM_WORD_SIZE]                                       :/ 1, // first 2 words
      [SRAM_WORD_SIZE+1 : sram_host_byte_size-1-SRAM_WORD_SIZE]  :/ 7,
      [sram_host_byte_size-SRAM_WORD_SIZE : sram_host_byte_size] :/ 1, // max 2 words
      [sram_host_byte_size+1 : SRAM_SIZE]                        :/ 1};// over the max size
  }

  constraint rx_watermark_lvl_c {
    rx_watermark_lvl dist {
      [0 : SRAM_WORD_SIZE]                                           :/ 1, // first 2 words
      [SRAM_WORD_SIZE+1 : sram_device_byte_size-1-SRAM_WORD_SIZE]    :/ 7,
      [sram_device_byte_size-SRAM_WORD_SIZE : sram_device_byte_size] :/ 1, // max 2 words
      [sram_device_byte_size+1 : SRAM_SIZE]                          :/ 1};// over the max size
  }

  // core clk freq / spi clk freq is from 1/4 to 8
  constraint freq_c {
    core_spi_freq_ratio inside {[1:8]};
    spi_freq_faster -> core_spi_freq_ratio <= 4;
  }

  `uvm_object_new

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    cfg.clk_rst_vif.wait_clks(1);
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if (do_spi_device_init) spi_device_init();
  endtask

  // check if any remaining data
  virtual task check_for_tx_rx_idle();
    uint tx_avail_bytes, rx_avail_bytes;
    read_tx_avail_bytes(SramDataAvail, tx_avail_bytes);
    `DV_CHECK_EQ(tx_avail_bytes, 0);
    read_rx_avail_bytes(SramDataAvail, rx_avail_bytes);
    `DV_CHECK_EQ(rx_avail_bytes, 0);
    csr_rd_check(.ptr(ral.status.rxf_empty), .compare_value(1));
    // level should be 0
    csr_rd_check(.ptr(ral.async_fifo_level.txlvl), .compare_value(0));
    csr_rd_check(.ptr(ral.async_fifo_level.rxlvl), .compare_value(0));
  endtask

  // NOTE on terminology
  // from spi_device IP perspective, tx is data sent out over sio[0] (device traffic from the IP),
  // rx is data received over sio[1] (host traffic from SPI agent)

  // TODO: use spi_device_pkg spi_mode enum instead
  virtual task spi_device_init();
    // set clk period
    if (spi_freq_faster) begin
      cfg.m_spi_agent_cfg.sck_period_ps = cfg.clk_rst_vif.clk_period_ps / core_spi_freq_ratio;
    end else begin
      cfg.m_spi_agent_cfg.sck_period_ps = cfg.clk_rst_vif.clk_period_ps * core_spi_freq_ratio;
    end
    // update host agent
    cfg.m_spi_agent_cfg.sck_polarity = sck_polarity;
    cfg.m_spi_agent_cfg.sck_phase = sck_phase;
    cfg.m_spi_agent_cfg.host_bit_dir = host_bit_dir;
    cfg.m_spi_agent_cfg.device_bit_dir = device_bit_dir;
    // update device rtl
    ral.control.mode.set(spi_mode);
    csr_update(.csr(ral.control));
    ral.cfg.cpol.set(sck_polarity);
    ral.cfg.cpha.set(sck_phase);
    ral.cfg.tx_order.set(device_bit_dir);
    ral.cfg.rx_order.set(host_bit_dir);
    //ral.cfg.timer_v.set(rx_timer); TODO do it later
    csr_update(.csr(ral.cfg));

    // watermark
    ral.fifo_level.txlvl.set(tx_watermark_lvl);
    ral.fifo_level.rxlvl.set(rx_watermark_lvl);
    csr_update(.csr(ral.fifo_level));

    // intr_enable
    `DV_CHECK_RANDOMIZE_FATAL(ral.intr_enable)
    csr_update(.csr(ral.intr_enable));

    if (do_spi_device_mem_cfg) begin
      set_sram_host_addr_range(sram_host_base_addr, sram_host_limit_addr);
      set_sram_device_addr_range(sram_device_base_addr, sram_device_limit_addr);
      // only configure sram once
      do_spi_device_mem_cfg = 0;
      sram_host_base_addr.rand_mode(0);
      sram_host_limit_addr.rand_mode(0);
      sram_device_base_addr.rand_mode(0);
      sram_device_limit_addr.rand_mode(0);
    end
  endtask

  virtual task reset_fifo(bit txfifo, bit rxfifo);
    ral.control.rst_txfifo.set(txfifo);
    ral.control.rst_rxfifo.set(rxfifo);
    csr_update(.csr(ral.control));
  endtask

  // set sram circular fifo limits for tx (spi_device)
  // args are 32 bits to be generic - corresponding fields are only 16 bits
  virtual task set_sram_device_addr_range(bit [31:0] base,
                                          bit [31:0] limit);
    ral.txf_addr.base.set(base);
    ral.txf_addr.limit.set(limit);
    csr_update(.csr(ral.txf_addr));
  endtask

  // set sram circular fifo limits for rx (host agant)
  // args are 32 bits to be generic - corresponding fields are only 16 bits
  virtual task set_sram_host_addr_range(bit [31:0] base,
                                        bit [31:0] limit);
    ral.rxf_addr.base.set(base);
    ral.rxf_addr.limit.set(limit);
    csr_update(.csr(ral.rxf_addr));
  endtask

  // set a byte of data via host agent, receive a byte of data from spi_device
  virtual task spi_host_xfer_byte(bit [7:0] host_data, ref bit [7:0] device_data);
    spi_host_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                   data.size() == 1;
                                   data[0]     == host_data;)
    `uvm_send(m_spi_host_seq)
    device_data = m_spi_host_seq.rsp.data[0];
  endtask

  // set a word (32 bits) of data via host agent, receive a word of data from spi_device
  virtual task spi_host_xfer_word(bit [31:0] host_data, ref bit [31:0] device_data);
    spi_host_seq m_spi_host_seq;
    byte data_bytes[SRAM_WORD_SIZE];
    {<<8{data_bytes}} = host_data;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                   data.size() == SRAM_WORD_SIZE;
                                   foreach (data[i]) {data[i] == data_bytes[i];})
    `uvm_send(m_spi_host_seq)
    device_data = {<<8{m_spi_host_seq.rsp.data}};
  endtask

  // set a random chunk of bytes of data via host agent and receive same number of data from device
  virtual task spi_host_xfer_bytes(int num_bytes = $urandom_range(1, 512),
                                   ref bit [7:0] device_data[$]);
    spi_host_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq, data.size() == num_bytes;)
    `uvm_send(m_spi_host_seq)
    device_data = m_spi_host_seq.rsp.data;
  endtask

  // write spi device data to send when incoming host traffic arrives
  virtual task write_device_words_to_send(bit [31:0] device_data[$]);
    bit [TL_DW-1:0] tx_wptr;
    uint tx_sram_size_bytes = `GET_TX_ALLOCATED_SRAM_SIZE_BYTES;

    // write data to tx base address + curr tx wptr
    tx_wptr = ral.txf_ptr.wptr.get_mirrored_value();
    foreach (device_data[i]) begin
      bit [TL_DW-1:0] tx_wptr_addr;
      bit [TL_DW-1:0] tx_base_addr = ral.txf_addr.base.get_mirrored_value();
      tx_base_addr[1:0] = 0; // ignore lower 2 bits
      tx_wptr_addr = cfg.sram_start_addr + tx_base_addr + tx_wptr[SRAM_MSB:0];
      `uvm_info(`gfn, $sformatf({"tx_wptr[SRAM_MSB:0] = 0x%0h, tx_wptr_phase_bit = 0x%0h, ",
                                 "tx_sram_size_bytes = 0x%0h, tx_wptr_addr = 0x%0h"},
                                 tx_wptr[SRAM_MSB:0], tx_wptr[SRAM_PTR_PHASE_BIT],
                                 tx_sram_size_bytes, tx_wptr_addr), UVM_MEDIUM)
      tl_access(.addr(tx_wptr_addr), .write(1'b1), .data(device_data[i])); // TODO: bkdr wr?

      // advance tx wptr by SRAM_WORD_SIZE
      tx_wptr = get_sram_new_ptr(.ptr(tx_wptr),
                                 .increment(SRAM_WORD_SIZE),
                                 .sram_size_bytes(tx_sram_size_bytes));
      `uvm_info(`gfn, $sformatf("new tx_wptr = 0x%0h", tx_wptr), UVM_MEDIUM)
    end

    // update txf_ptr.wptr
    tx_wptr = get_csr_val_with_updated_field(ral.txf_ptr.wptr, ral.txf_ptr.get(), tx_wptr);
    csr_wr(.ptr(ral.txf_ptr), .value(tx_wptr));
  endtask

  // read spi host data received from the host
  virtual task read_host_words_rcvd(uint num_words, ref bit [31:0] host_data[$]);
    bit [TL_DW-1:0] rx_rptr;
    uint rx_sram_size_bytes = `GET_RX_ALLOCATED_SRAM_SIZE_BYTES;

    // read data from rx base address + curr rptr
    rx_rptr = ral.rxf_ptr.rptr.get_mirrored_value();
    repeat (num_words) begin
      bit   [TL_DW-1:0] rx_rptr_addr;
      bit   [TL_DW-1:0] word_data;
      bit   [TL_DW-1:0] rx_base_addr = ral.rxf_addr.base.get_mirrored_value();
      rx_base_addr[1:0] = 0; // ignore lower 2 bits
      rx_rptr_addr = cfg.sram_start_addr + rx_base_addr + rx_rptr[SRAM_MSB:0];
      `uvm_info(`gfn, $sformatf({"rx_rptr[SRAM_MSB:0] = 0x%0h, rx_rptr_phase_bit = 0x%0h, ",
                                 "rx_sram_size_bytes = 0x%0h, rx_rptr_addr = 0x%0h"},
                                 rx_rptr[SRAM_MSB:0], rx_rptr[SRAM_PTR_PHASE_BIT],
                                 rx_sram_size_bytes, rx_rptr_addr), UVM_MEDIUM)
      tl_access(.addr(rx_rptr_addr), .write(1'b0), .data(word_data)); // TODO: bkdr rd?
      host_data.push_back(word_data);
      // advance rx rptr by SRAM_WORD_SIZE
      rx_rptr = get_sram_new_ptr(.ptr(rx_rptr),
                                 .increment(SRAM_WORD_SIZE),
                                 .sram_size_bytes(rx_sram_size_bytes));
      `uvm_info(`gfn, $sformatf("new rx_rptr = 0x%0h", rx_rptr), UVM_MEDIUM)
    end

    // update rxf_ptr.rptr
    csr_wr(.ptr(ral.rxf_ptr), .value(rx_rptr));
  endtask

  virtual task read_tx_avail_bytes(sram_avail_type_e avail_type, ref uint avail_bytes);
    bit [TL_DW-1:0] rptr;
    bit [TL_DW-1:0] wptr;
    uint            sram_size_bytes = `GET_TX_ALLOCATED_SRAM_SIZE_BYTES;

    csr_rd(.ptr(ral.txf_ptr.rptr), .value(rptr));
    wptr = ral.txf_ptr.wptr.get_mirrored_value();
    case(avail_type)
      SramDataAvail: begin
        avail_bytes = get_sram_filled_bytes(wptr, rptr, sram_size_bytes, "read_tx_avail_bytes");
        // if sram has no data, check async fifo level
        if (avail_bytes == 0) begin
          uint fifo_lvl;
          csr_rd(.ptr(ral.async_fifo_level.txlvl), .value(fifo_lvl));
          avail_bytes += fifo_lvl;
        end
      end
      SramSpaceAvail: begin
        avail_bytes = get_sram_space_bytes(wptr, rptr, sram_size_bytes, "read_tx_avail_bytes");
      end
    endcase
    `uvm_info(`gfn, $sformatf("TX avail_type = %0s, avail_bytes = %0d",
                              avail_type.name, avail_bytes), UVM_MEDIUM)
  endtask

  virtual task read_rx_avail_bytes(sram_avail_type_e avail_type, ref uint avail_bytes);
    bit [TL_DW-1:0] rptr;
    bit [TL_DW-1:0] wptr;
    uint            sram_size_bytes = `GET_RX_ALLOCATED_SRAM_SIZE_BYTES;

    csr_rd(.ptr(ral.rxf_ptr.wptr), .value(wptr));
    rptr = ral.rxf_ptr.rptr.get_mirrored_value();
    case(avail_type)
      SramDataAvail: begin
        avail_bytes = get_sram_filled_bytes(wptr, rptr, sram_size_bytes, "read_rx_avail_bytes");
      end
      SramSpaceAvail: begin
        avail_bytes = get_sram_space_bytes(wptr, rptr, sram_size_bytes, "read_rx_avail_bytes");
      end
    endcase
    `uvm_info(`gfn, $sformatf("RX avail_type = %0s, avail_bytes = %0d",
                              avail_type.name, avail_bytes), UVM_MEDIUM)
  endtask

  virtual task wait_for_tx_avail_bytes(uint req_bytes, sram_avail_type_e avail_type,
                                       ref uint avail_bytes);
    uint cur_bytes;
    `DV_SPINWAIT(
      do begin
        read_tx_avail_bytes(avail_type, cur_bytes);
      end while (cur_bytes < req_bytes);,
      {"wait_for_tx_avail_bytes::", avail_type.name},
      default_timeout_ns * 2
    )
    avail_bytes = cur_bytes;
    `uvm_info(`gfn, $sformatf("TX req_bytes = %0d, avail_type = %0s, avail_bytes = %0d",
                              req_bytes, avail_type.name, avail_bytes), UVM_MEDIUM)
  endtask

  virtual task wait_for_rx_avail_bytes(uint req_bytes, sram_avail_type_e avail_type,
                                       ref uint avail_bytes);
    uint cur_bytes;
    `DV_SPINWAIT(
      do begin
        read_rx_avail_bytes(avail_type, cur_bytes);
      end while (cur_bytes < req_bytes);,
      {"wait_for_rx_avail_bytes::", avail_type.name},
      default_timeout_ns * 2
    )
    avail_bytes = cur_bytes;
    `uvm_info(`gfn, $sformatf("RX req_bytes = %0d, avail_type = %0s, avail_bytes = %0d",
                              req_bytes, avail_type.name, avail_bytes), UVM_MEDIUM)
  endtask

  // before spi host starts transfer, wait for tx to have enough data and rx to have enough space
  // to avoid overflow and underflow
  virtual task wait_for_tx_filled_rx_space_bytes(uint req_bytes, ref uint avail_bytes);
    uint tx_avail_bytes, rx_avail_bytes;
    fork
      wait_for_tx_avail_bytes(req_bytes, SramDataAvail, tx_avail_bytes);
      wait_for_rx_avail_bytes(req_bytes, SramSpaceAvail, rx_avail_bytes);
    join
    // return the less number
    avail_bytes = (tx_avail_bytes < rx_avail_bytes) ? tx_avail_bytes : rx_avail_bytes;
  endtask

  // before spi host starts transfer, check if tx has enough data and rx has enough space
  // if return_out_of_range = 1, return more than actual available bytes
  virtual task get_num_xfer_bytes(bit return_out_of_range, ref uint avail_bytes);
    uint tx_avail_bytes, rx_avail_bytes, final_data_bytes;

    read_tx_avail_bytes(SramDataAvail, tx_avail_bytes);
    read_rx_avail_bytes(SramSpaceAvail, rx_avail_bytes);
    // get the less number to avoid under/overflow
    avail_bytes = (tx_avail_bytes < rx_avail_bytes) ? tx_avail_bytes : rx_avail_bytes;

    if (return_out_of_range) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(final_data_bytes,
                                         final_data_bytes[1:0] == 0;
                                         final_data_bytes inside {[avail_bytes+1:SRAM_SIZE]};)
      avail_bytes = final_data_bytes;
    end
  endtask

endclass : spi_device_base_vseq
