// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_scoreboard extends cip_base_scoreboard #(.CFG_T (spi_device_env_cfg),
                                                          .RAL_T (spi_device_reg_block),
                                                          .COV_T (spi_device_env_cov));
  `uvm_component_utils(spi_device_scoreboard)

  // TLM fifos to pick up the packets
  uvm_tlm_analysis_fifo #(spi_item) host_spi_data_fifo;
  uvm_tlm_analysis_fifo #(spi_item) device_spi_data_fifo;

  // mem model to save expected value
  mem_model tx_mem;
  mem_model rx_mem;
  uint tx_rptr_exp;
  uint rx_wptr_exp;

  // tx/rx fifo, size is 2 words
  bit [31:0] tx_word_fifo[$];
  bit [31:0] rx_word_fifo[$];

  // local queues to hold incoming packets pending comparison
  spi_item host_spi_data_q[$];
  spi_item device_spi_data_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_spi_data_fifo = new("host_spi_data_fifo", this);
    device_spi_data_fifo = new("device_spi_data_fifo", this);
    tx_mem = mem_model#()::type_id::create("tx_mem", this);
    rx_mem = mem_model#()::type_id::create("rx_mem", this);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_host_spi_fifo();
      process_device_spi_fifo();
    join_none
  endtask

  // extract spi items sent from host
  virtual task process_host_spi_fifo();
    spi_item item;
    forever begin
      host_spi_data_fifo.get(item);
      receive_spi_rx_data({item.data[3], item.data[2], item.data[1], item.data[0]});
      `uvm_info(`gfn, $sformatf("received host spi item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  // extract spi items sent from device
  virtual task process_device_spi_fifo();
    spi_item item;
    forever begin
      device_spi_data_fifo.get(item);
      sendout_spi_tx_data({item.data[3], item.data[2], item.data[1], item.data[0]});
      `uvm_info(`gfn, $sformatf("received device spi item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  // process_tl_access:this task processes incoming access into the IP over tl interface
  // this is already called in cip_base_scoreboard::process_tl_a/d_chan_fifo tasks
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check   = 1'b0; // TODO: fixme
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = get_normalized_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else if (item.a_addr inside {[cfg.sram_start_addr:cfg.sram_end_addr]}) begin
      uint tx_base  = ral.txf_addr.base.get_mirrored_value();
      uint rx_base  = ral.rxf_addr.base.get_mirrored_value();
      uint tx_limit = ral.txf_addr.limit.get_mirrored_value();
      uint rx_limit = ral.rxf_addr.limit.get_mirrored_value();
      uint mem_addr = item.a_addr - cfg.sram_start_addr;
      tx_base[1:0] = 0;
      rx_base[1:0] = 0;
      if (mem_addr inside {[tx_base : tx_base + tx_limit]}) begin // TX address
        if (write && channel == AddrChannel) begin
          tx_mem.write(mem_addr - tx_base, item.a_data);
          `uvm_info(`gfn, $sformatf("write tx_mem addr 0x%0h, data: 0x%0h",
                                    mem_addr - tx_base, item.a_data), UVM_MEDIUM)
        end
      end else if (mem_addr inside {[rx_base : rx_base + rx_limit]}) begin // RX address
        if (write && channel == AddrChannel) begin
          `uvm_error(`gfn, "unexpected write on RX mem")
        end else if (!write && channel == DataChannel) begin
          uint            addr     = mem_addr - rx_base;
          bit [TL_DW-1:0] data_exp = rx_mem.read(addr);
          `DV_CHECK_EQ(item.d_data, data_exp, $sformatf("Compare SPI RX data, addr: 0x%0h", addr))
        end
      end else begin
        // TODO hit unlocated mem, sample coverage
      end
      return;
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (write && channel == AddrChannel) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    case (csr.get_name())
      "txf_ptr": begin
        if (write && channel == AddrChannel) begin
          update_tx_fifo_and_rptr();
        end
      end
      "rxf_ptr": begin
        if (write && channel == AddrChannel) begin
          update_rx_mem_fifo_and_wptr();
        end
      end
      // TODO the other regs
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data)
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  // read data from mem then update tx fifo and tx_rptr
  virtual function void update_tx_fifo_and_rptr();
    uint filled_bytes = get_tx_sram_filled_bytes();
    // move data to fifo
    while (tx_word_fifo.size < 2 && filled_bytes >= SRAM_WORD_SIZE) begin
      tx_word_fifo.push_back(tx_mem.read(tx_rptr_exp[SRAM_MSB:0]));
      `uvm_info(`gfn, $sformatf("write tx_word_fifo rptr 0x%0h, data: 0x%0h",
                               tx_rptr_exp, tx_mem.read(tx_rptr_exp[SRAM_MSB:0])), UVM_MEDIUM)
      tx_rptr_exp = get_sram_new_ptr(.ptr(tx_rptr_exp),
                                     .increment(SRAM_WORD_SIZE),
                                     .sram_size_bytes(`get_tx_allocated_sram_size_bytes));
      filled_bytes -= SRAM_WORD_SIZE;
    end
  endfunction

  // send out SPI data from tx_fifo and fetch more data from sram to fifo
  virtual function void sendout_spi_tx_data(bit [31:0] data_act);

    if (tx_word_fifo.size > 0) begin
      bit [31:0] data_exp     = tx_word_fifo.pop_front();
      `DV_CHECK_EQ(data_act, data_exp, "Compare SPI TX data")
      update_tx_fifo_and_rptr();
    end else begin // underflow
      // TODO coverage sample
      `uvm_info(`gfn, $sformatf("TX underflow data: 0x%0h", data_act), UVM_MEDIUM)
    end
  endfunction

  // when receive a spi rx data, save it in rx_fifo and then write to rx_mem
  // when rx_fifo is full (size=2) and no space in sram, drop it
  virtual function void receive_spi_rx_data(bit [TL_DW:0] data);
    if (get_rx_sram_space_bytes() >= SRAM_WORD_SIZE || rx_word_fifo.size < 2) begin
      rx_word_fifo.push_back(data);
      update_rx_mem_fifo_and_wptr();
    end
    else begin
      `uvm_info(`gfn, $sformatf("RX overflow data: 0x%0h ptr: 0x%0h", data, rx_wptr_exp),
                UVM_MEDIUM)
    end
  endfunction

  // update rx mem, fifo and wptr when receive a spi trans or when rptr is updated
  virtual function void update_rx_mem_fifo_and_wptr();
    uint space_bytes = get_rx_sram_space_bytes();
    // move from fifo to mem
    while (rx_word_fifo.size > 0 && space_bytes >= SRAM_WORD_SIZE) begin
      bit [TL_DW:0] data = rx_word_fifo.pop_front();
      rx_mem.write(rx_wptr_exp[SRAM_MSB:0], data);
      `uvm_info(`gfn, $sformatf("write rx_mem, addr 0x%0h, data: 0x%0h",
                                rx_wptr_exp, data), UVM_MEDIUM)
      rx_wptr_exp = get_sram_new_ptr(.ptr(rx_wptr_exp),
                                     .increment(SRAM_WORD_SIZE),
                                     .sram_size_bytes(`get_rx_allocated_sram_size_bytes));
      space_bytes -= SRAM_WORD_SIZE;
    end
  endfunction

  virtual function uint get_tx_sram_filled_bytes();
    uint tx_wptr      = ral.txf_ptr.wptr.get_mirrored_value();
    uint filled_bytes = get_sram_filled_bytes(tx_wptr,
                                              tx_rptr_exp,
                                              `get_tx_allocated_sram_size_bytes,
                                              {`gfn, "::get_tx_sram_filled_bytes"});
    return filled_bytes;
  endfunction

  virtual function uint get_rx_sram_space_bytes();
    uint rx_rptr     = ral.rxf_ptr.rptr.get_mirrored_value();
    uint space_bytes = get_sram_space_bytes(rx_wptr_exp,
                                            rx_rptr,
                                            `get_rx_allocated_sram_size_bytes,
                                            {`gfn, "::get_rx_sram_space_bytes"});
    return space_bytes;
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    tx_rptr_exp = ral.txf_ptr.rptr.get_reset();
    rx_wptr_exp = ral.rxf_ptr.wptr.get_reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
  endfunction

endclass
