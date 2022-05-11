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
  uvm_tlm_analysis_fifo #(spi_item) downstream_spi_host_data_fifo;
  uvm_tlm_analysis_fifo #(spi_item) downstream_spi_device_data_fifo;

  // mem model to save expected value
  local mem_model tx_mem;
  local mem_model rx_mem;
  local uint tx_rptr_exp;
  local uint rx_wptr_exp;

  // expected values
  local bit [NumSpiDevIntr-1:0] intr_exp;

  // tx/rx fifo, size is 2 words
  local bit [31:0] tx_word_q[$];
  local bit [31:0] rx_word_q[$];

  local bit [7:0] pass_opcode;
  local bit [7:0] host_opcode;
  local bit [7:0] pass_addr_q[$];
  local bit [7:0] pass_pld_q[$];
  local bit pass_enabled;

  local spi_item host_items_q[$];
  local spi_item pass_items_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_spi_data_fifo = new("host_spi_data_fifo", this);
    device_spi_data_fifo = new("device_spi_data_fifo", this);
    downstream_spi_host_data_fifo = new("downstream_spi_host_data_fifo", this);
    downstream_spi_device_data_fifo = new("downstream_spi_device_data_fifo", this);
    tx_mem = mem_model#()::type_id::create("tx_mem", this);
    rx_mem = mem_model#()::type_id::create("rx_mem", this);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_host_spi_fifo();
      process_device_spi_fifo();
      process_pass_spi_fifo();
    join_none
  endtask

  // extract spi items sent from host
  virtual task process_host_spi_fifo();
    spi_item item;
    bit [4:0] cmd_position;
    bit [4:0] cmd_offset;
    forever begin
      host_spi_data_fifo.get(item);
      if (cfg.m_spi_agent_cfg.fw_flash == 0) begin
        receive_spi_rx_data({item.data[3], item.data[2], item.data[1], item.data[0]});
      end
      if (cfg.m_spi_agent_cfg.fw_flash == 1) begin
        host_items_q.push_back(item);
        host_opcode = item.opcode;
        if (`gmv(ral.control.mode) == PassthroughMode) begin
          // If opcode is added to config it is enabled
          if (cfg.m_spi_agent_cfg.cmd_infos[host_opcode].op_code == host_opcode) begin
            pass_enabled = 1;
          end else begin
            host_items_q.delete();
          end
          cmd_position = host_opcode / 32;
          cmd_offset = host_opcode % 32;
          // If opcode is filtered in filter register it is disabled
          if (`gmv(ral.cmd_filter[cmd_position].filter[cmd_offset]) == 1) begin
            pass_enabled = 0;
            host_items_q.delete();
          end
          if (cfg.m_spi_agent_cfg.cmd_infos[host_opcode].write_command == 0) begin
            for (int i = 0; i < item.payload_q.size(); i++) begin
              `DV_CHECK_EQ(item.payload_q[i], pass_items_q[0].payload_q[i], "Check Read Pass Data")
            end
          end
        end
        pass_items_q.delete();
      end
      `uvm_info(`gfn, $sformatf("received host spi item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  // extract spi items sent from device
  virtual task process_device_spi_fifo();
    spi_item item;
    forever begin
      device_spi_data_fifo.get(item);
      if (cfg.m_spi_agent_cfg.num_bytes_per_trans_in_mon == 4) begin
        sendout_spi_tx_data({item.data[3], item.data[2], item.data[1], item.data[0]});
      end
      `uvm_info(`gfn, $sformatf("received device spi item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  virtual task process_pass_spi_fifo();
    spi_item item;
    int shift;
    forever begin
      fork
        begin : item_collection_thread
          downstream_spi_host_data_fifo.get(item);
          pass_items_q.push_back(item);
          `uvm_info(`gfn, $sformatf("received pass spi item:\n%0s", item.sprint()), UVM_HIGH)
          if (`gmv(ral.control.mode) == PassthroughMode) begin
            pass_opcode = item.opcode;
            // Compare OPCODE
            `DV_CHECK_EQ(pass_opcode, host_opcode, "Compare PASSTHROUGH Opcode")
            if (pass_enabled == 1) begin
              pass_addr_q = item.address_q;
              // Compare address - possible addr bits swap
              compare_pass_addr(pass_addr_q);
              shift = 1 + cfg.m_spi_agent_cfg.cmd_infos[host_opcode].addr_bytes;
              if (cfg.m_spi_agent_cfg.cmd_infos[host_opcode].write_command == 1) begin
                if (item.payload_q.size() >= 4) begin
                  pass_pld_q = {item.payload_q[3], item.payload_q[2], item.payload_q[1],
                               item.payload_q[0]};
                  // Compare first payload word - possible bit swap
                  compare_first_word(pass_pld_q);
                end
                // Remaining payload must be the same if pass command
                for (int i = 4; i < item.payload_q.size(); i++) begin
                  `DV_CHECK_EQ(item.payload_q[i], host_items_q[0].payload_q[i],
                            "Check Payload Byte")
                end
              end
            end
            host_items_q.delete();
            pass_pld_q.delete();
            pass_addr_q.delete();
          end
        end
      join_any
    end
  endtask

  // process_tl_access:this task processes incoming access into the IP over tl interface
  // this is already called in cip_base_scoreboard::process_tl_a/d_chan_fifo tasks
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b0; // TODO: fixme
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
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
        if (!write && channel == DataChannel) begin //TODO UVM_ERROR unexpected write on RX mem
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
      "intr_test": begin
        if (write && channel == AddrChannel) begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          intr_exp |= item.a_data;
          if (cfg.en_cov) begin
            foreach (intr_exp[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
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
    while (tx_word_q.size < 2 && filled_bytes >= SRAM_WORD_SIZE) begin
      tx_word_q.push_back(tx_mem.read(tx_rptr_exp[SRAM_MSB:0]));
      `uvm_info(`gfn, $sformatf("write tx_word_q rptr 0x%0h, data: 0x%0h",
                               tx_rptr_exp, tx_mem.read(tx_rptr_exp[SRAM_MSB:0])), UVM_MEDIUM)
      tx_rptr_exp = get_sram_new_ptr(.ptr(tx_rptr_exp),
                                     .increment(SRAM_WORD_SIZE),
                                     .sram_size_bytes(`GET_TX_ALLOCATED_SRAM_SIZE_BYTES));
      filled_bytes -= SRAM_WORD_SIZE;
    end
  endfunction

  // send out SPI data from tx_fifo and fetch more data from sram to fifo
  virtual function void sendout_spi_tx_data(bit [31:0] data_act);

    if (tx_word_q.size > 0) begin
      bit [31:0] data_exp     = tx_word_q.pop_front();
      if (cfg.m_spi_agent_cfg.bits_to_transfer == 7) begin
        if (cfg.m_spi_agent_cfg.device_bit_dir == 1)  begin
          data_exp[7] = 0;
        end else begin
          data_exp[0] = 0;
        end
      end
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
    if (get_rx_sram_space_bytes() >= SRAM_WORD_SIZE || rx_word_q.size < 2) begin
      rx_word_q.push_back(data);
      if (`gmv(ral.control.mode) != PassthroughMode) begin
        update_rx_mem_fifo_and_wptr();
      end
    end
    else begin
      `uvm_info(`gfn, $sformatf("RX overflow data: 0x%0h ptr: 0x%0h", data, rx_wptr_exp),
                UVM_MEDIUM)
    end
  endfunction

  // Task that compares passthrough addrss
  virtual function void compare_pass_addr(bit [7:0] address[$]);
    bit enabled;
    bit [31:0] mask_swap = `gmv(ral.addr_swap_mask.mask);
    bit [31:0] data_swap = `gmv(ral.addr_swap_data.data);
    bit [31:0] addr_exp;
    if (address.size() == 3) begin
      addr_exp = {host_items_q[0].address_q[2], host_items_q[0].address_q[1],
                  host_items_q[0].address_q[0]};
    end
    if (address.size() == 4) begin
      addr_exp = {host_items_q[0].address_q[3], host_items_q[0].address_q[2],
                  host_items_q[0].address_q[1], host_items_q[0].address_q[0]};
    end
    if (cfg.m_spi_agent_cfg.cmd_infos[host_opcode].addr_swap == 1) begin // Addr Swap enable
      for (int i = 0; i < 32; i++) begin
        if (mask_swap[i] == 1) begin
          addr_exp[i] = data_swap[i];
        end
      end
    end
    if (address.size() == 3) begin
      `DV_CHECK_EQ({address[2], address[1], address[0]}, addr_exp[23:0],
                   "Compare PASSTHROUGH Address")
    end
    if (address.size() == 4) begin
      `DV_CHECK_EQ({address[3], address[2], address[1], address[0]}, addr_exp[31:0],
                   "Compare PASSTHROUGH Address")
    end
  endfunction

  // Task that compares passthrough payload first word
  virtual function void compare_first_word(bit [7:0] payload[$]);
    bit enabled;
    bit [4:0] en_idx;
    bit [31:0] mask_swap = `gmv(ral.payload_swap_mask.mask);
    bit [31:0] data_swap = `gmv(ral.payload_swap_data.data);
    bit [31:0] data_exp;
    data_exp = {host_items_q[0].payload_q[3], host_items_q[0].payload_q[2],
                host_items_q[0].payload_q[1], host_items_q[0].payload_q[0]};
    if (cfg.m_spi_agent_cfg.cmd_infos[host_opcode].data_swap == 1) begin // Addr Swap enable
      for (int i = 0; i < 32; i++) begin
        if (mask_swap[i] == 1) begin
          data_exp[i] = data_swap[i];
        end
      end
    end
    `DV_CHECK_EQ({payload[3], payload[2], payload[1], payload[0]}, data_exp[31:0],
                 "Compare PASSTHROUGH Payload")
  endfunction

  // update rx mem, fifo and wptr when receive a spi trans or when rptr is updated
  virtual function void update_rx_mem_fifo_and_wptr();
    uint space_bytes = get_rx_sram_space_bytes();
    // move from fifo to mem
    while (rx_word_q.size > 0 && space_bytes >= SRAM_WORD_SIZE) begin
      bit [TL_DW:0] data = rx_word_q.pop_front();
      rx_mem.write(rx_wptr_exp[SRAM_MSB:0], data);
      `uvm_info(`gfn, $sformatf("write rx_mem, addr 0x%0h, data: 0x%0h",
                                rx_wptr_exp, data), UVM_MEDIUM)
      rx_wptr_exp = get_sram_new_ptr(.ptr(rx_wptr_exp),
                                     .increment(SRAM_WORD_SIZE),
                                     .sram_size_bytes(`GET_RX_ALLOCATED_SRAM_SIZE_BYTES));
      space_bytes -= SRAM_WORD_SIZE;
    end
  endfunction

  virtual function uint get_tx_sram_filled_bytes();
    uint tx_wptr      = ral.txf_ptr.wptr.get_mirrored_value();
    uint filled_bytes = get_sram_filled_bytes(tx_wptr,
                                              tx_rptr_exp,
                                              `GET_TX_ALLOCATED_SRAM_SIZE_BYTES,
                                              {`gfn, "::get_tx_sram_filled_bytes"});
    return filled_bytes;
  endfunction

  virtual function uint get_rx_sram_space_bytes();
    uint rx_rptr     = ral.rxf_ptr.rptr.get_mirrored_value();
    uint space_bytes = get_sram_space_bytes(rx_wptr_exp,
                                            rx_rptr,
                                            `GET_RX_ALLOCATED_SRAM_SIZE_BYTES,
                                            {`gfn, "::get_rx_sram_space_bytes"});
    return space_bytes;
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    tx_rptr_exp = ral.txf_ptr.rptr.get_reset();
    rx_wptr_exp = ral.rxf_ptr.wptr.get_reset();
    intr_exp    = ral.intr_state.get_reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, host_spi_data_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, device_spi_data_fifo)
    `DV_CHECK_EQ(tx_word_q.size, 0)
    `DV_CHECK_EQ(rx_word_q.size, 0)
  endfunction

endclass
