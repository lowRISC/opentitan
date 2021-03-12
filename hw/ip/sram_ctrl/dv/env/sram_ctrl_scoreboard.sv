// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(sram_ctrl_env_cfg),
    .RAL_T(sram_ctrl_reg_block),
    .COV_T(sram_ctrl_env_cov)
  );
  `uvm_component_utils(sram_ctrl_scoreboard)
  `uvm_component_new

  // local variables

  typedef struct {
    // 1 for writes, 0 for reads
    bit we;

    // TLUL address
    bit [TL_AW-1:0] addr;

    // Contains either the requested write data
    // or the read response data
    bit [TL_DW-1:0] data;

    // only writes are masked, all reads are full-word
    bit [TL_DBW-1:0] mask;

    // Tag the memory transaction with the appropriate key and nonce,
    // so that we can keep track even if a new key is requested
    otp_ctrl_pkg::sram_key_t key;
    otp_ctrl_pkg::sram_nonce_t nonce;

  } sram_trans_t;

  // TLM agent fifos for the tl_agent connected to the SRAM memory itself
  uvm_tlm_analysis_fifo #(tl_seq_item) sram_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) sram_tl_d_chan_fifo;

  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(KDI_DATA_SIZE))) kdi_fifo;

  // local queues to hold incoming packets pending comparison

  // store addr_phase information about incoming transaction
  mailbox #(sram_trans_t) addr_phase_mbox;

  // mailbox that all completed sram_trans_t structs will be pushed into for processing.
  //
  // transaction order in this mailbox represents the orderr in which the underlying memory
  // will actually perform memory operations, taking into account any forwarding/reordering.
  //
  // Use mailbox to enforce atomic FIFO ordering.
  mailbox #(sram_trans_t) completed_trans_mbox;

  otp_ctrl_pkg::sram_key_t key     = sram_ctrl_pkg::RndCnstSramKeyDefault;
  otp_ctrl_pkg::sram_nonce_t nonce = sram_ctrl_pkg::RndCnstSramNonceDefault;

  // Data holding "register" and transaction info for use in forwarding situations
  // e.g. if a write is followed by a read, the write transaction is held
  //      and is not immediately reflected in the memory macro
  sram_trans_t held_trans;

  // the held data is assumed to be masked correctly, to deal with tricky situations where
  // a read follows b2b writes of the same address (each with different masks) -
  // we need to be able to have access to the most updated version of the write data
  bit [TL_DW-1:0] held_data;

  bit in_raw_hazard = 0;

  // utility function to word-align an input TL address
  // (SRAM is indexed at word granularity)
  function bit [TL_AW-1:0] word_align_addr(bit [TL_AW-1:0] addr);
    return {addr[TL_AW-1:2], 2'b00};
  endfunction

  // utility function to check whether two addresses map to the same SRAM memory line
  function bit eq_sram_addr(bit [TL_AW-1:0] addr1, bit [TL_AW-1:0] addr2);
    bit [TL_AW-1:0] addr_mask = '0;

    addr1 = word_align_addr(addr1);
    addr2 = word_align_addr(addr2);

    for (int i = 0; i < cfg.mem_bkdr_vif.mem_addr_width + 2; i++) begin
      addr_mask[i] = 1;
    end

    return (addr1 & addr_mask) == (addr2 & addr_mask);
  endfunction

  // utility function to reset all fields of a sram_trans_t
  function void clear_trans(ref sram_trans_t t);
    t.we    = 0;
    t.addr  = '0;
    t.data  = '0;
    t.mask  = '0;
    t.key   = sram_ctrl_pkg::RndCnstSramKeyDefault;
    t.nonce = sram_ctrl_pkg::RndCnstSramNonceDefault;
  endfunction

  // utility function to clear all RAW hazard state
  function void clear_hazard_state();
    in_raw_hazard = 0;
    held_data = '0;
    clear_trans(held_trans);
  endfunction

  // utility function to expand a TLUL mask to a full bit-mask
  function bit [TL_DW-1:0] expand_bit_mask(bit [TL_DBW-1:0] mask);
    bit [TL_DW-1:0] bitmask = '0;
    for (int i = 0; i < TL_DBW; i++) begin
      bitmask[i*8 +: 8] = {8{mask[i]}};
    end
    return bitmask;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sram_tl_a_chan_fifo = new("sram_tl_a_chan_fifo", this);
    sram_tl_d_chan_fifo = new("sram_tl_d_chan_fifo", this);

    kdi_fifo = new("kdi_fifo", this);

    addr_phase_mbox = new();
    completed_trans_mbox = new();
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_sram_tl_a_chan_fifo();
      process_sram_tl_d_chan_fifo();
      process_kdi_fifo();
      process_completed_trans();
    join_none
  endtask

  virtual task process_sram_tl_a_chan_fifo();
    tl_seq_item item;
    sram_trans_t addr_trans;
    forever begin
      if (cfg.en_scb) begin

        if (sram_tl_a_chan_fifo.try_get(item) > 0) begin // received a tl_seq_item
          `uvm_info(`gfn, $sformatf("Received sram_tl_a_chan item:\n%0s", item.sprint()), UVM_HIGH)

          // TODO: need to ensure that we don't process TLUL errors

          addr_trans.we    = item.is_write();
          addr_trans.addr  = word_align_addr(item.a_addr);
          addr_trans.mask  = item.a_mask;
          addr_trans.key   = key;
          addr_trans.nonce = nonce;
          if (item.is_write()) begin
            addr_trans.data = item.a_data;
          end

          // write the addr_trans into the mailbox
          addr_phase_mbox.put(addr_trans);

          `uvm_info({`gfn, "::process_sram_tl_a_chan_fifo()"},
                    $sformatf("Put ADDR_PHASE transaction into addr_phase_mbox: %0p", addr_trans),
                    UVM_HIGH)

          // terminate the raw_hazard status if we see this series of mem accesses -
          // `write -> 1+ reads -> write`, where we are currently looking at
          // the final `write` transaction
          //
          // in this case, we should send the held write transaction off to be checked,
          // and not do anything to the pending address transaction currently in the address phase
          //
          // we also need to lower `in_raw_hazard` as we no longer require data forwarding
          cfg.clk_rst_vif.wait_n_clks(1);
          if (in_raw_hazard && addr_trans.we) begin
            `uvm_info(`gfn, "next b2b transaction is a write, clearing hazard state", UVM_HIGH)
            completed_trans_mbox.put(held_trans);
            clear_hazard_state();
          end
        end else begin // didn't receive tl_seq_item

          // terminate the raw_hazard status in the scenario:
          // `write -> 1+ reads -> empty cycle` - if an empty cycle occurs after the last read
          // transaction that causes a hazard, the write will be resolved during this cycle,
          // so clear the hazard status and check the held write transaction
          if (in_raw_hazard) begin
            `uvm_info(`gfn, "Empty cycle seen after hazardous read, clearing hazard state", UVM_HIGH)
            completed_trans_mbox.put(held_trans);
            clear_hazard_state();
          end
        end

      end

      // wait a cycle before next non-blocking check to sram_tl_a_chan
      cfg.clk_rst_vif.wait_clks(1);
      // small delay to allow monitor to complete putting item into sram_tl_a_chan_fifo
      #1;
    end
  endtask

  virtual task process_sram_tl_d_chan_fifo();
    tl_seq_item item;
    sram_trans_t addr_trans;
    sram_trans_t data_trans;

    forever begin
      sram_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("Received sram_tl_d_chan item:\n%0s", item.sprint()), UVM_HIGH)

      // TODO: need to ensure that we don't process TLUL errors

      // check packet integrity
      void'(item.is_ok());

      // the addr_phase_mbox will be populated during A_phase of each memory transaction.
      //
      // since we use the addr_phase_mbox in this task to check for data forwarding hazards,
      // need to keep it up to date with the current transaction.
      //
      // it is guaranteed that both:
      // - the mailbox will have at least 1 addr_trans item in it at this point
      // - the first item in the mailbox matches up to the current data_phase transaction
      //
      // as a result we can safely remove the item from the mailbox here
      `DV_CHECK_NE(addr_phase_mbox.try_get(addr_trans), 0,
        "AddrPhase transaction not available in addr_phase_mbox")

      // assign data_trans fields
      clear_trans(data_trans);
      data_trans.addr  = word_align_addr(item.a_addr);
      data_trans.mask  = item.a_mask;
      data_trans.key   = key;
      data_trans.nonce = nonce;

      `uvm_info(`gfn, $sformatf("in_raw_hazard: %0d",  in_raw_hazard), UVM_HIGH)

      if (item.d_opcode == tlul_pkg::AccessAckData) begin // read
        `uvm_info(`gfn, "Processing READ transaction", UVM_HIGH)

        data_trans.we = 0;
        data_trans.data = item.d_data;

        if (in_raw_hazard) begin
          // executing a read while `in_raw_hazard` is high means that this read comes after
          // the most recent write transaction, which has then been held
          //
          // as a result we need to check for an address collision then act accordingly.

          // if we have an address collision (read address is the same as the pending write address)
          // return data based on the `held_data`
          if (eq_sram_addr(data_trans.addr, held_trans.addr)) begin
            bit [TL_DW-1:0] exp_masked_rdata = held_data & expand_bit_mask(item.a_mask);
            `uvm_info(`gfn, $sformatf("exp_masked_rdata: 0x%0x", exp_masked_rdata), UVM_HIGH)
            `DV_CHECK_EQ_FATAL(exp_masked_rdata, item.d_data)
          end else begin
            // in this case we do not have a strict RAW hazard on the same address,
            // so we can check the read transaction normally, as it will complete
            // before the pending write
            completed_trans_mbox.put(data_trans);
          end

        end else begin
          completed_trans_mbox.put(data_trans);
        end
      end else if (item.d_opcode == tlul_pkg::AccessAck) begin // write
        bit b2b_detected;

        `uvm_info(`gfn, "Processing WRITE transaction", UVM_HIGH)

        data_trans.we = 1;
        data_trans.data = item.a_data;

        // insert a small delay before checking addr_phase_mbox to allow b2b
        // transactions to be picked up (otherwise we wait until the next cycle)
        #1;

        // peek at the next address phase request
        b2b_detected = addr_phase_mbox.try_peek(addr_trans);
        `uvm_info(`gfn, $sformatf("b2b_detected: %0d", b2b_detected), UVM_HIGH)

        if (b2b_detected) begin

          bit  [TL_AW-1:0] waddr = '0;

          `uvm_info(`gfn, $sformatf("addr_trans: %0p", addr_trans), UVM_HIGH)

          if (addr_trans.we == 0) begin
            // if we see a read directly after a write and we are not currently in a RAW hazard
            // handling state, we need to do the following:
            //
            // - backdoor read the memory at the given address to get the currently stored data,
            //   and update the scb data holding "register" with this value
            //
            // - overwrite this data holding register with the masked write data sent by the
            //   original write transaction that caused the forwarding scenario (this is so that
            //   sub-word reads reading different bytes from the ones being written can still
            //   return the most recently written values)
            `uvm_info(`gfn, "detected RAW hazard", UVM_HIGH)
            in_raw_hazard = 1;
            held_trans = data_trans;
            waddr = {data_trans.addr[TL_AW-1:2], 2'b00};
            held_data = cfg.mem_bkdr_vif.sram_encrypt_read32(waddr, data_trans.key, data_trans.nonce);

            for (int i = 0; i < TL_DBW; i++) begin
              if (data_trans.mask[i]) begin
                held_data[i*8 +: 8] = data_trans.data[i*8 +: 8];
              end
            end
            `uvm_info(`gfn, $sformatf("new held_data: 0x%0x", held_data), UVM_HIGH)
          end else begin
            // if we have a write-after-write scenario, whether the addresses are the same or not,
            // just proceed as normal and send the current transaction off to be checked
            completed_trans_mbox.put(data_trans);
          end
        end else begin
          // if no b2b transaction detected, it is safe to send
          // the collected transaction off for checking
          completed_trans_mbox.put(data_trans);
        end
      end
    end
  endtask

  // This task polls the kdi_fifo for completed key request transactions
  virtual task process_kdi_fifo();
    bit seed_valid;
    push_pull_item #(.DeviceDataWidth(KDI_DATA_SIZE)) item;
    forever begin
      kdi_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received transaction from kdi_fifo:\n%0s", item.convert2string()), UVM_HIGH)

      // When KDI item is seen, update key, nonce
      //
      // TODO: update STATUS.scr_key_seed_valid
      {key, nonce, seed_valid} = item.d_data;

      `uvm_info(`gfn, $sformatf("Updated key: 0x%0x", key), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("Updated nonce: 0x%0x", nonce), UVM_HIGH)
    end
  endtask

  // This task continuously pulls items from the completed_trans_mbox
  // and checks them for correctness by using the mem_bkdr_if.
  //
  // TLUL allows partial reads and writes, so we first need to construct a bit-mask
  // based off of the TLUL mask field.
  // We then read from the memory using the backdoor interface, and can then directly compare
  // the TLUL response data to the backdoor-read data using the bit-mask.
  virtual task process_completed_trans();
    sram_trans_t trans;

    forever begin
      completed_trans_mbox.get(trans);

      `uvm_info({`gfn, "::process_completed_trans()"},
                $sformatf("Checking SRAM memory transaction: %0p", trans),
                UVM_HIGH)

      check_mem_trans(trans);
    end
  endtask

  // Given a complete memory transaction item as input,
  // this function compares against the SRAM for correctness
  // using the mem_bkdr_if.
  //
  // TLUL allows partial reads and writes, so we first need to construct a bit-mask
  // based off of the TLUL mask field.
  // We then read from the memory using the backdoor interface, and can then directly compare
  // the TLUL response data to the backdoor-read data using the bit-mask.
  virtual function void check_mem_trans(sram_trans_t t);
    bit [TL_AW-1:0] word_addr;
    bit [TL_DW-1:0] bit_mask;

    // data read from SRAM through backdoor
    bit [TL_DW-1:0] exp_data;
    bit [TL_DW-1:0] exp_masked_data;
    bit [TL_DW-1:0] act_masked_data;


    // Word align the request address
    word_addr = {t.addr[TL_AW-1:2], 2'b00};
    `uvm_info(`gfn, $sformatf("word_addr: 0x%0x", word_addr), UVM_HIGH)

    bit_mask = expand_bit_mask(t.mask);

    // backdoor read the mem
    exp_data = cfg.mem_bkdr_vif.sram_encrypt_read32(word_addr, t.key, t.nonce);
    `uvm_info(`gfn, $sformatf("exp_data: 0x%0x", exp_data), UVM_HIGH)

    exp_masked_data = exp_data & bit_mask;
    act_masked_data = t.data & bit_mask;

    `uvm_info(`gfn, $sformatf("exp_masked_data: 0x%0x", exp_masked_data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("act_masked_data: 0x%0x", act_masked_data), UVM_HIGH)

    `DV_CHECK_EQ_FATAL(exp_masked_data, act_masked_data)
  endfunction


  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "exec_regwen": begin
        // do nothing
      end
      "exec": begin
      end
      "status": begin
        // TODO
        do_read_check = 1'b0;
      end
      "ctrl_regwen": begin
        // do nothing
      end
      "ctrl": begin
        // do nothing if 0 is written
        if (addr_phase_write && item.a_data) begin
        end
      end
      "error_address": begin
        // TODO
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    clear_hazard_state();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, sram_tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, sram_tl_d_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(push_pull_item#(.DeviceDataWidth(KDI_DATA_SIZE)), kdi_fifo)
    `DV_CHECK_EQ(addr_phase_mbox.num(), 0, "Items still remain in addr_phase_mbox!")
    `DV_CHECK_EQ(completed_trans_mbox.num(), 0, "Items still remain in completed_trans_mbox!")
  endfunction

endclass
