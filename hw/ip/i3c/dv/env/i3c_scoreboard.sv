// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The scoreboard does not model I3C behaviour yet. It keeps the RAL mirror up to date with the
// register accesses, so that sequences can use the mirrored values, checks reads from the memory
// windows, and relies on the base class for the TL-UL error and alert checks.
class i3c_scoreboard extends cip_base_scoreboard #(
    .CFG_T(i3c_env_cfg),
    .RAL_T(i3c_reg_block),
    .COV_T(i3c_env_cov)
  );
  `uvm_component_utils(i3c_scoreboard)

  // Addresses of the message buffer bytes whose expected value is known (see process_mem_write()).
  protected bit buffer_byte_known[uvm_reg_addr_t];

  // Tracking of the hardware writes to the message buffer memory, indexed by word address:
  // - The number of hardware writes to each word.
  protected int unsigned buffer_hw_wr_cnt[int unsigned];
  // - For each software write that has reached the memory but whose TL-UL response has not been
  //   processed yet, the number of hardware writes to the word at the time of the software write.
  protected int unsigned buffer_sw_wr_snap[int unsigned][$];

  // Masks of the stored bits in each word of a DAT and a DCT entry; the reserved fields of the
  // entries read as zero.
  protected uvm_reg_data_t dat_word_masks[$];
  protected uvm_reg_data_t dct_word_masks[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    get_dat_word_masks(dat_word_masks);
    get_dct_word_masks(dct_word_masks);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      monitor_buffer_writes();
    join_none
  endtask

  // Track the writes to the message buffer memory.
  //
  // The hardware queues store their data in the message buffer, so the hardware writes to it
  // whenever data enters a queue, e.g. through a queue port or on an Asynchronous Event. Such a
  // write makes the expected value of the word unknown. For each software write, record how many
  // hardware writes the word has seen when the software write reaches the memory, so that
  // process_mem_write() can tell whether a hardware write came between the software write and
  // its TL-UL response.
  protected virtual task monitor_buffer_writes();
    forever begin
      @(cfg.buf_mon_vif.cb);
      if (!cfg.buf_mon_vif.cb.rst_ni || !cfg.buf_mon_vif.cb.we) continue;
      if (cfg.buf_mon_vif.cb.sw) begin
        buffer_sw_wr_snap[cfg.buf_mon_vif.cb.addr].push_back(
            buffer_hw_wr_cnt[cfg.buf_mon_vif.cb.addr]);
      end else begin
        uvm_reg_addr_t byte_addr = ral.buffer.get_address() + 4 * cfg.buf_mon_vif.cb.addr;
        buffer_hw_wr_cnt[cfg.buf_mon_vif.cb.addr]++;
        for (int i = 0; i < TL_DBW; i++) buffer_byte_known.delete(byte_addr + i);
      end
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // Software writes that are still pending will not complete.
    buffer_sw_wr_snap.delete();
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    bit            write    = item.is_write();

    csr = cfg.ral_models[ral_name].get_default_map().get_reg_by_offset(csr_addr);
    // Accesses to the memory windows are handled in process_mem_write() and mem_compare().
    if (csr == null) return;

    if (write && channel == AddrChannel) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      // Both interrupts are of status type: INTR_STATE reflects the value last written to
      // INTR_TEST, in addition to the interrupts that the hardware signals.
      if (csr == ral.intr_test && item.a_mask[0]) begin
        void'(ral.intr_state.predict(.value(item.a_data), .kind(UVM_PREDICT_DIRECT)));
      end
    end
    // Keep the predicted value of INTR_STATE rather than the value read, so that sequences that
    // check the interrupt outputs against the mirrored value (such as intr_test) compare them
    // against the prediction.
    if (!write && channel == DataChannel && csr != ral.intr_state) begin
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  // Without a model of the I3C behaviour, the mirrored values of hardware-updated registers are
  // not reliable, so only check reads from INTR_STATE, for the interrupts that the hardware cannot
  // signal.
  virtual function void do_read_check(dv_base_reg dv_reg, tl_seq_item item);
    uvm_reg_data_t mask;
    if (dv_reg != ral.intr_state) return;
    mask = get_intr_state_check_mask();
    `DV_CHECK_EQ(item.d_data & mask, `gmv(ral.intr_state) & mask,
                 "INTR_STATE does not match the value written to INTR_TEST")
  endfunction

  // Return the mask of the INTR_STATE bits whose value is known: the hardware cannot signal an
  // interrupt while all the signal enables of its sources are clear.
  protected function uvm_reg_data_t get_intr_state_check_mask();
    uvm_reg_data_t mask = '0;
    if (`gmv(ral.intr_signal_enable) == 0 && `gmv(ral.pio_intr_signal_enable) == 0 &&
        `gmv(ral.stby_cr_intr_signal_enable) == 0) begin
      mask[IntrHci] = 1'b1;
    end
    if (`gmv(ral.targ_intr_signal_enable) == 0) mask[IntrTarg] = 1'b1;
    return mask;
  endfunction

  // Return whether mem is one of the windows onto the HCI and TTI queue ports.
  protected function bit is_queue_port(uvm_mem mem);
    return mem == ral.hci_ports || mem == ral.tti_ports;
  endfunction

  virtual task process_mem_write(tl_seq_item item, string ral_name);
    dv_base_reg_block block     = cfg.ral_models[ral_name];
    uvm_reg_addr_t    norm_addr = block.get_normalized_addr(item.a_addr);
    dv_base_mem       mem       = get_mem_at_addr(block, norm_addr);

    if (mem == null || is_queue_port(mem)) return;

    super.process_mem_write(item, ral_name);
    if (mem == ral.buffer && !cfg.under_reset) begin
      int unsigned word_addr = (norm_addr - mem.get_address()) >> 2;
      int unsigned hw_wr_cnt;
      bit          known;
      // The expected value is known unless the hardware has written the word since this write
      // reached the memory.
      if (buffer_sw_wr_snap.exists(word_addr) && buffer_sw_wr_snap[word_addr].size() > 0) begin
        hw_wr_cnt = buffer_sw_wr_snap[word_addr].pop_front();
        known     = (hw_wr_cnt == buffer_hw_wr_cnt[word_addr]);
      end
      for (int i = 0; i < TL_DBW; i++) begin
        if (!item.a_mask[i]) continue;
        if (known) buffer_byte_known[norm_addr + i] = 1'b1;
        else       buffer_byte_known.delete(norm_addr + i);
      end
    end
  endtask

  virtual function void mem_compare(string ral_name, uvm_reg_addr_t addr, tl_seq_item item);
    dv_base_mem    mem      = get_mem_at_addr(cfg.ral_models[ral_name], addr);
    uvm_reg_data_t bit_mask = '1;
    uvm_reg_addr_t word_idx;

    // Reads from the queue ports return queue entries, not previously written data.
    if (mem == null || is_queue_port(mem)) return;

    word_idx = (addr - mem.get_address()) >> 2;
    if (mem == ral.dat) bit_mask = dat_word_masks[word_idx % dat_word_masks.size()];
    if (mem == ral.dct) bit_mask = dct_word_masks[word_idx % dct_word_masks.size()];

    for (int i = 0; i < TL_DBW; i++) begin
      bit [7:0] byte_mask = bit_mask[i*8 +: 8];
      if (!item.a_mask[i]) continue;
      if (mem == ral.buffer && !buffer_byte_known.exists(addr + i)) continue;
      `DV_CHECK_EQ(item.d_data[i*8 +: 8] & byte_mask,
                   exp_mem[ral_name].read_byte(addr + i) & byte_mask,
                   $sformatf("Read data mismatch in %0s at address 0x%0h",
                             mem.get_name(), addr + i))
    end
  endfunction

endclass
