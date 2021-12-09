// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_scoreboard #(parameter int AddrWidth = 10) extends cip_base_scoreboard #(
    .CFG_T(sram_ctrl_env_cfg#(AddrWidth)),
    .RAL_T(sram_ctrl_regs_reg_block),
    .COV_T(sram_ctrl_env_cov#(AddrWidth))
  );
  `uvm_component_param_utils(sram_ctrl_scoreboard#(AddrWidth))
  `uvm_component_new

  // local variables

  bit [TL_DW-1:0] exp_status = '0;

  bit in_key_req = 0;

  // this bit goes high for the duration of memory initialization
  bit in_init = 0;

  // This bit goes high as soon as a LC escalation request is seen on the interface,
  // and goes low once the scoreboard has finished all internal handling logic up to
  // resetting the key and nonce (one cycle after `exp_status` is updated).
  bit handling_lc_esc;

  // this bit goes high immediately after waiting for
  // LC_ESCALATION_PROPAGATION_DELAY cycles, to signal that
  // the LC escalation has finished propagating through the design
  bit status_lc_esc;

  // internal state for executable-mode information
  bit       allow_ifetch;

  // The values detected from interface and EXEC csr writes - are not immediately valid
  // as they need to be "latched" by the internal scb logic whenever an addr_phase_write
  // is detected on the sram_tl_a_chan_fifo.
  bit [3:0] detected_csr_exec = '0;
  bit [3:0] detected_hw_debug_en = '0;
  bit [7:0] detected_en_sram_ifetch = '0;

  // The values that are "latched" by sram_tl_a_chan_fifo and are assumed to be valid
  bit [3:0] valid_csr_exec;
  bit [3:0] valid_hw_debug_en;
  bit [7:0] valid_en_sram_ifetch;

  bit in_executable_mode;

  // path for backdoor access
  string write_en_path;
  string write_addr_path;

  sram_ctrl_mem_bkdr_scb mem_bkdr_scb;

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

  typedef struct {
    bit [TL_AW-1:0]  addr;
    bit [TL_DW-1:0]  data;
    bit [TL_DBW-1:0] mask;
  } mem_item_t;

  mem_item_t write_item_q[$];

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

  bit [TL_AW-1:0] sram_addr_mask = (1 << (AddrWidth + 2)) - 1;

  // utility function to word-align an input TL address
  // (SRAM is indexed at word granularity)
  function bit [TL_AW-1:0] word_align_addr(bit [TL_AW-1:0] addr);
    return {addr[TL_AW-1:2], 2'b00};
  endfunction

  // Only LSB is used in the sram, the other MSB bits will be ignored. Use the simplified
  // address for mem_bkdr_scb
  function bit [TL_AW-1:0] simplify_addr(bit [TL_AW-1:0] addr);
    // word align
    addr[1:0] = 0;
    return addr & sram_addr_mask;
  endfunction

  function bit [AddrWidth-1:0] decrypt_sram_addr(bit [AddrWidth-1:0] addr);
    logic addr_arr         [] = new[AddrWidth];
    logic decrypt_addr_arr [] = new[AddrWidth];
    logic nonce_arr        [] = new[$bits(otp_ctrl_pkg::sram_nonce_t)];

    addr_arr  = {<<{addr}};
    nonce_arr = {<<{nonce}};

    decrypt_addr_arr = sram_scrambler_pkg::decrypt_sram_addr(addr_arr, AddrWidth, nonce_arr);

    return {<<{decrypt_addr_arr}};
  endfunction

  // utility function to check whether two addresses map to the same SRAM memory line
  function bit eq_sram_addr(bit [TL_AW-1:0] addr1, bit [TL_AW-1:0] addr2);
    bit [TL_AW-1:0] addr_mask = '0;

    addr1 = word_align_addr(addr1);
    addr2 = word_align_addr(addr2);

    for (int i = 0; i < cfg.mem_bkdr_util_h.get_addr_width() + 2; i++) begin
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

  // utility function used by `process_sram_tl_d_chan_fifo()` to check that
  // the current data_phase transaction matches the transaction pulled from the `addr_phase_mbox`
  //
  // can also be more generally used to check equality of two transactions
  function bit eq_trans(sram_trans_t t1, sram_trans_t t2);
    bit equal = (t1.we == t2.we) && (eq_sram_addr(t1.addr, t2.addr)) &&
                (t1.mask == t2.mask) && (t1.key == t2.key) && (t1.nonce == t2.nonce);
    `uvm_info(`gfn, $sformatf("Comparing 2 transactions:\nt1: %0p\nt2: %0p", t1, t2), UVM_HIGH)
    // as one of the sram_trans_t structs will be still in address phase,
    // it may not have the data field available if it is a READ operation
    //
    // in this case, only compare the data field if these are write transactions
    return (equal && t1.we) ? (equal && (t1.data == t2.data)) : equal;
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

  // Check if the input tl_seq_item has any tl errors.
  //
  // NOTE: this function is designed to only work for tl_seq_item objects sent to the
  //       TLUL interface of the SRAM scrambling memory, as this interface does not
  //       care about CSR/uvm_mem addressing.
  //       For the same reason, we cannot use the already-provided `predict_tl_err(...)`
  //       function of the cip_base_scoreboard, as the SRAM TLUL interface does not have
  //       any CSRs or uvm_mems.
  virtual function bit get_sram_instr_type_err(tl_seq_item item, tl_channels_e channel);
    bit is_tl_err;
    tlul_pkg::tl_a_user_t a_user = tlul_pkg::tl_a_user_t'(item.a_user);

    if (a_user.instr_type == prim_mubi_pkg::MuBi4True) begin
      // 2 error cases if an InstrType transaction is seen:
      // - if it is a write transaction
      // - if the SRAM is not configured in executable mode
      is_tl_err = (allow_ifetch) ? (item.a_opcode != tlul_pkg::Get) : 1'b1;
    end

    if (channel == DataChannel && is_tl_err) begin
      `DV_CHECK_EQ(item.d_error, 1, $sformatf("item_err: %0d", is_tl_err))
    end

    return is_tl_err;
  endfunction

  virtual function bit predict_tl_err(tl_seq_item item, tl_channels_e channel, string ral_name);
    if (ral_name == cfg.sram_ral_name && get_sram_instr_type_err(item, channel)) return 1;
    return super.predict_tl_err(item, channel, ral_name);
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
    string mem_path = dv_utils_pkg::get_parent_hier(cfg.mem_bkdr_util_h.get_path());
    write_en_path   = $sformatf("%s.write_i", mem_path);
    write_addr_path = $sformatf("%s.addr_i", mem_path);
    `DV_CHECK(uvm_hdl_check_path(write_en_path),
              $sformatf("Hierarchical path %0s appears to be invalid.", write_en_path))
    `DV_CHECK(uvm_hdl_check_path(write_addr_path),
              $sformatf("Hierarchical path %0s appears to be invalid.", write_addr_path))

    mem_bkdr_scb = sram_ctrl_mem_bkdr_scb::type_id::create("mem_bkdr_scb");
    mem_bkdr_scb.mem_bkdr_util_h = cfg.mem_bkdr_util_h;

    super.run_phase(phase);
    fork
      sample_key_req_access_cg();
      process_sram_init();
      process_lc_escalation();
      process_sram_executable();
      process_sram_tl_a_chan_fifo();
      process_sram_tl_d_chan_fifo();
      process_kdi_fifo();
      process_completed_trans();
      process_write_done_and_check();
    join_none
  endtask

  // write usually completes in a few cycles after TL addrss phase, but it may take longer time
  // when it's partial write or when RAW hazard occurs. It's not easy to know when it actually
  // finishes, so probe internal write_i instead
  task process_write_done_and_check();
    forever begin
      bit write_en;
      mem_item_t item;
      bit [AddrWidth-1:0] write_addr;
      bit [TL_AW-1:0] sram_addr;

      wait (write_item_q.size > 0);
      item = write_item_q.pop_front();

      while (!write_en) begin
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK(uvm_hdl_read(write_en_path, write_en))
      end
      `DV_CHECK(uvm_hdl_read(write_addr_path, write_addr))
      sram_addr = decrypt_sram_addr(write_addr);

      sram_addr = sram_addr << 2;

      // the data should be settled after posedge. Wait for a 1ps to avoid race condition
      cfg.clk_rst_vif.wait_clks(1);
      #1ps;
      mem_bkdr_scb.write_finish(sram_addr, item.mask);
    end
  endtask

  // This task spins forever and samples the appropriate covergroup whenever
  // in_key_req is high and a new valid addr_phase transaction is seen on the memory bus.
  virtual task sample_key_req_access_cg();
    forever begin
      @(negedge cfg.under_reset);
      `DV_SPINWAIT_EXIT(
          forever begin
            @(posedge in_key_req);
            `DV_SPINWAIT_EXIT(
                forever begin
                  // sample the covergroup every time a new TL request is seen
                  // while a key request is outstanding.
                  @(posedge cfg.m_tl_agent_cfgs[cfg.sram_ral_name].vif.h2d.a_valid);
                  // zero delay to allow bus values to settle
                  #0;
                  if (cfg.en_cov) begin
                    cov.access_during_key_req_cg.sample(
                        cfg.m_tl_agent_cfgs[cfg.sram_ral_name].vif.h2d.a_opcode);
                  end
                end
                ,
                @(negedge in_key_req);
            )
          end
          ,
          wait(cfg.under_reset == 1);
      )
    end
  endtask

  virtual task process_sram_init();
    // SRAM initialization happens once at the beginning of each simulation and requires a key to be
    // provisioned from OTP first.
    // As a result we simply just wait for the first key request to end, and then wait for each line
    // of the memory to be written.
    forever begin
      wait(!cfg.under_reset);
      @(posedge in_init);
      // clear the init done signal
      exp_status[SramCtrlInitDone] = 0;
      // initialization process only starts once the corresponding key request finishes
      @(negedge in_key_req);
      // initialization process will randomize each line in the SRAM, one cycle each
      //
      // thus we just need to wait for a number of cycles equal to the total size
      // of the sram address space
      `uvm_info(`gfn, "starting to wait for init", UVM_HIGH)
      cfg.clk_rst_vif.wait_clks(cfg.mem_bkdr_util_h.get_depth());
      // Wait a small delay to latch the updated CSR status
      #1;
      // if we are in escalated state, scr_key_seed_valid will always stay low. otherwise
      // we can set the init done flag here.
      exp_status[SramCtrlInitDone] = status_lc_esc ? 0 : 1;
      in_init = 0;
      `uvm_info(`gfn, "dropped in_init", UVM_HIGH)
    end
  endtask

  virtual task process_lc_escalation();
    forever begin
      wait(cfg.lc_vif.lc_esc_en == lc_ctrl_pkg::On);
      `uvm_info(`gfn, "LC escalation request detected", UVM_HIGH)

      handling_lc_esc = 1;

      // escalation signal needs 3 cycles to be propagated through the DUT
      cfg.clk_rst_vif.wait_clks(LC_ESCALATION_PROPAGATION_CYCLES);

      // signal that the escalation propagation has finished.
      //
      // updated control signals should now be broadcast from `sram_ctrl`
      // to the rest of the SRAM subsystem
      status_lc_esc = 1;

      // Though the updated STATUS fields, key, and nonce are available
      // LC_ESCALATION_PROPAGATION_CYCLES after detecting an escalation request,
      // these values only become valid on the cycle after that.
      //
      // We wait a cycle here so the invalid values do not corrupt scoreboard state.
      cfg.clk_rst_vif.wait_clks(1);

      exp_status[SramCtrlEscalated]       = 1;
      exp_status[SramCtrlScrKeySeedValid] = 0;
      exp_status[SramCtrlScrKeyValid]     = 0;
      exp_status[SramCtrlInitDone]        = 0;

      // escalation resets the key and nonce back to defaults
      key   = sram_ctrl_pkg::RndCnstSramKeyDefault;
      nonce = sram_ctrl_pkg::RndCnstSramNonceDefault;

      // insert a small delay before dropping `handling_lc_esc`.
      //
      // This indicates that the scoreboard is done handling the internal updates required
      // by an escalation request.
      //
      // However, this also has the effect of letting us handle a particularly tricky edge
      // case where a memory request is sent on the cycle before `status_lc_esc` goes high.
      // (see issue lowRISC/opentitan#5590).
      //
      // In this scenario, the `sram_tl_d_chan_fifo` will get the valid response tl_seq_item from
      // the SRAM's TL response channel.
      // As per issue #5590, even though the response is perfectly valid, any read data will be
      // corrupted/incorrect due to the key input to `PRINCE` switching mid-way through keystream
      // generation.
      // This means that there will be a valid `sram_trans_t` item in `addr_phase_mbox` that we need
      // to ignore as it will be corrupted, so we use `handling_lc_esc` as an indicator of when we
      // can safely throw an error if an unexpected `tl_seq_item` is received by the
      // `sram_tl_d_chan_fifo`.
      //
      // Again as per #5590, even if a write is performed successfully in this edge case it is ok to
      // ignore it - we technically do not care about the write as the SRAM must be reset anyways
      // before any more valid accesses can be made.
      #1 handling_lc_esc = 0;

      // lc escalation status will be dropped after reset, no further action needed
      wait(cfg.lc_vif.lc_esc_en == lc_ctrl_pkg::Off);

      // sample coverage
      if (cfg.en_cov) begin
        cov.lc_escalation_rst_cg.sample(cfg.clk_rst_vif.rst_n);
      end
    end
  endtask

  virtual task process_sram_executable();
    forever begin
      @(cfg.exec_vif.lc_hw_debug_en, cfg.exec_vif.otp_en_sram_ifetch, detected_csr_exec);

      // "latch" these values with a slight delay to ensure everything has settled
      #1;

      detected_hw_debug_en = cfg.exec_vif.lc_hw_debug_en;
      detected_en_sram_ifetch = cfg.exec_vif.otp_en_sram_ifetch;

      // sample executability-related coverage
      if (cfg.en_cov) begin
        cov.executable_cg.sample(detected_hw_debug_en,
                                 detected_en_sram_ifetch,
                                 detected_csr_exec);
      end

      `uvm_info(`gfn, $sformatf("detected_hw_debug_en: %0b", detected_hw_debug_en), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("detected_en_sram_ifetch: %0b", detected_en_sram_ifetch), UVM_HIGH)

    end
  endtask

  virtual task process_sram_tl_a_chan_fifo();
    tl_seq_item item;
    sram_trans_t addr_trans;
    forever begin
      if (sram_tl_a_chan_fifo.try_get(item) > 0) begin // received a tl_seq_item
        `uvm_info(`gfn, $sformatf("Received sram_tl_a_chan item:\n%0s", item.sprint()), UVM_HIGH)

        // update internal state related to instruction type and SRAM execution
        valid_csr_exec = detected_csr_exec;
        valid_hw_debug_en = detected_hw_debug_en;
        valid_en_sram_ifetch = detected_en_sram_ifetch;

        if (`INSTR_EXEC) begin
          allow_ifetch = (valid_en_sram_ifetch == prim_mubi_pkg::MuBi8True) ?
                         (valid_csr_exec == prim_mubi_pkg::MuBi4True)       :
                         (valid_hw_debug_en == lc_ctrl_pkg::On);
        end else begin
          allow_ifetch = 0;
        end

        if (!cfg.en_scb) continue;

        `DV_CHECK_EQ(in_key_req, 0, "No item is accepted during key req")
        `DV_CHECK_EQ(in_init, 0, "No item is accepted during init")

        // If the escalation propagation has finished,
        // do not process anymore addr_phase transactions
        if (status_lc_esc) continue;

        // don't process any error items
        //
        // TODO: sample error coverage
        if (cfg.en_scb_tl_err_chk && predict_tl_err(item, AddrChannel, cfg.sram_ral_name)) begin
          `uvm_info(`gfn, "TL addr_phase error detected", UVM_HIGH)
          continue;
        end

        if (item.is_write()) begin
          mem_bkdr_scb.write_start(simplify_addr(item.a_addr), item.a_data, item.a_mask);

          write_item_q.push_back(mem_item_t'{simplify_addr(item.a_addr),
                                             item.a_data, item.a_mask});
        end else begin
          mem_bkdr_scb.read_start(simplify_addr(item.a_addr), item.a_mask);
        end

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
        if (in_raw_hazard && !status_lc_esc) begin
          `uvm_info(`gfn, "Empty cycle seen after hazardous read, clearing hazard state", UVM_HIGH)
          completed_trans_mbox.put(held_trans);
          clear_hazard_state();
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

    bit addr_trans_available = 0;

    forever begin
      sram_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("Received sram_tl_d_chan item:\n%0s", item.sprint()), UVM_HIGH)

      // don't process any error items
      //
      // TODO: sample error coverage
      if (cfg.en_scb_tl_err_chk && predict_tl_err(item, DataChannel, cfg.sram_ral_name)) begin
        `uvm_info(`gfn, "TL data_phase error detected", UVM_HIGH)
        continue;
      end

      // check packet integrity
      void'(item.is_ok());

      addr_trans_available = (addr_phase_mbox.try_get(addr_trans) > 0);

      `DV_CHECK_EQ(in_key_req, 0, "No item is accepted during key req")
      `DV_CHECK_EQ(in_init, 0, "No item is accepted during init")

      // See the explanation in `process_lc_escalation()` as to why we use `handling_lc_esc`.
      //
      // Excepting this edge case, detecting any other item in the `addr_phase_mbox` indicates that
      // a TLUL response has been seen from the SRAM even though it hasn't been processed by
      // `process_sram_tl_a_chan_fifo()`. This means one of two things:
      //
      // 1) There is a bug in the scoreboard.
      //
      // 2) There is a bug in the design and the SRAM is actually servicing memory requests
      //    while in the terminal escalated state.
      if (status_lc_esc) begin
        if (handling_lc_esc) begin
          continue;
        end else begin
          `DV_CHECK_EQ(addr_trans_available, 1,
              "SRAM returned TLUL response in LC escalation state")
        end
      end

      if (!item.is_write()) begin
        mem_bkdr_scb.read_finish(item.d_data, simplify_addr(item.a_addr), item.a_mask);
      end

      // the addr_phase_mbox will be populated during A_phase of each memory transaction.
      //
      // since we use the addr_phase_mbox in this task to check for data forwarding hazards,
      // need to keep it up to date with the current transaction.
      //
      // it is guaranteed that both:
      // - the mailbox will have at least 1 addr_trans item in it at this point
      // - the first item in the mailbox matches up to the current data_phase transaction
      //
      // as a result we can safely remove the item from the mailbox here,
      // and check that the addr_trans and data_trans correspond to the same TLUL operation
      `DV_CHECK_NE(addr_trans_available, 0,
        "AddrPhase transaction not available in addr_phase_mbox")

      // assign data_trans fields
      clear_trans(data_trans);
      data_trans.we    = item.is_write();
      data_trans.addr  = word_align_addr(item.a_addr);
      data_trans.mask  = item.a_mask;
      data_trans.key   = addr_trans.key;
      data_trans.nonce = addr_trans.nonce;
      data_trans.data  = item.is_write() ? item.a_data : item.d_data;
      `DV_CHECK_EQ(eq_trans(addr_trans, data_trans), 1)

      `uvm_info(`gfn, $sformatf("in_raw_hazard: %0d",  in_raw_hazard), UVM_HIGH)

      if (!item.is_write()) begin // read
        `uvm_info(`gfn, "Processing READ transaction", UVM_HIGH)

        if (in_raw_hazard) begin
          // executing a read while `in_raw_hazard` is high means that this read comes after
          // the most recent write transaction, which has then been held
          //
          // as a result we need to check for an address collision then act accordingly.

          // sample b2b-related coovergroup
          if (cfg.en_cov) begin
            cov.b2b_access_types_cg.sample(data_trans.we, addr_trans.we);
          end

          // if we have an address collision (read address is the same as the pending write address)
          // return data based on the `held_data`
          if (eq_sram_addr(data_trans.addr, held_trans.addr)) begin
            bit [TL_DW-1:0] bit_mask = expand_bit_mask(item.a_mask);
            bit [TL_DW-1:0] exp_masked_rdata = held_data & bit_mask;
            `uvm_info(`gfn, $sformatf("exp_masked_rdata: 0x%0x", exp_masked_rdata), UVM_HIGH)
            `DV_CHECK_EQ_FATAL(exp_masked_rdata, item.d_data & bit_mask)
          end else begin
            // in this case we do not have a strict RAW hazard on the same address,
            // so we can check the read transaction normally, as it will complete
            // before the pending write
            completed_trans_mbox.put(data_trans);
          end

        end else begin
          completed_trans_mbox.put(data_trans);
        end
      end else if (item.is_write()) begin // write
        bit b2b_detected;

        `uvm_info(`gfn, "Processing WRITE transaction", UVM_HIGH)

        // insert a small delay before checking addr_phase_mbox to allow b2b
        // transactions to be picked up (otherwise we wait until the next cycle)
        #1;

        // peek at the next address phase request
        b2b_detected = addr_phase_mbox.try_peek(addr_trans);
        `uvm_info(`gfn, $sformatf("b2b_detected: %0d", b2b_detected), UVM_HIGH)

        if (b2b_detected) begin

          bit  [TL_AW-1:0] waddr = '0;

          `uvm_info(`gfn, $sformatf("addr_trans: %0p", addr_trans), UVM_HIGH)

          // sample b2b-related covergroup
          if (cfg.en_cov) begin
            cov.b2b_access_types_cg.sample(data_trans.we, addr_trans.we);
          end

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
            held_data = cfg.mem_bkdr_util_h.sram_encrypt_read32_integ(waddr, data_trans.key,
                                                                      data_trans.nonce);

            // sample covergroup
            if (cfg.en_cov) begin
              cov.raw_hazard_cg.sample(waddr == word_align_addr(addr_trans.addr));
            end

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

      // after a KDI transaction is completed, it takes 3 clock cycles in the SRAM domain
      // to properly synchronize and propagate the data through the DUT
      cfg.clk_rst_vif.wait_clks(KDI_PROPAGATION_CYCLES + 1);

      // Wait a small delay before updating CSR status
      #1;

      in_key_req = 0;
      `uvm_info(`gfn, "dropped in_key_req", UVM_HIGH)

      // When KDI item is seen, update key, nonce
      {key, nonce, seed_valid} = item.d_data;
      mem_bkdr_scb.update_key(key, nonce);

      // sample coverage on seed_valid
      if (cfg.en_cov) begin
        cov.key_seed_valid_cg.sample(status_lc_esc, seed_valid);
      end

      // scr_key_valid simply denotes that a successful handshake with OTP has completed,
      // so this will be 1 whenever we get a copmleted transaction item
      exp_status[SramCtrlScrKeyValid]     = 1;

      // if we are in escalated state, scr_key_seed_valid will always stay low
      exp_status[SramCtrlScrKeySeedValid] = status_lc_esc ? 0 : seed_valid;

      `uvm_info(`gfn, $sformatf("Updated key: 0x%0x", key), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("Updated nonce: 0x%0x", nonce), UVM_HIGH)
    end
  endtask

  // This task continuously pulls items from the completed_trans_mbox
  // and checks them for correctness by using the mem_bkdr_util.
  //
  // TLUL allows partial reads and writes, so we first need to construct a bit-mask
  // based off of the TLUL mask field.
  // We then read from the memory using the backdoor interface, and can then directly compare
  // the TLUL response data to the backdoor-read data using the bit-mask.
  virtual task process_completed_trans();
    sram_trans_t trans;

    forever begin
      completed_trans_mbox.get(trans);

      // sample access granularity for each completed transaction
      if (cfg.en_cov) begin
        cov.subword_access_cg.sample(trans.we, trans.mask);
      end

      `uvm_info({`gfn, "::process_completed_trans()"},
                $sformatf("Checking SRAM memory transaction: %0p", trans),
                UVM_MEDIUM)

      check_mem_trans(trans);
    end
  endtask

  // Given a complete memory transaction item as input,
  // this function compares against the SRAM for correctness
  // using the mem_bkdr_util.
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
    exp_data = cfg.mem_bkdr_util_h.sram_encrypt_read32_integ(word_addr, t.key, t.nonce);
    `uvm_info(`gfn, $sformatf("exp_data: 0x%0x", exp_data), UVM_MEDIUM)

    exp_masked_data = exp_data & bit_mask;
    act_masked_data = t.data & bit_mask;

    `uvm_info(`gfn, $sformatf("exp_masked_data: 0x%0x", exp_masked_data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("act_masked_data: 0x%0x", act_masked_data), UVM_HIGH)

    // TODO, downgrade this check and it can't handle a few b2b cases
    // This part of checking will be removed once mem_bkdr_scb works well.
    if (exp_masked_data != act_masked_data) begin
      `uvm_info(`gfn, $sformatf("act_masked_data: 0x%0x != exp_masked_data: 0x%0x",
                                act_masked_data, exp_masked_data), UVM_LOW)
    end
  endfunction


  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    if (ral_name != RAL_T::type_name) return;

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
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
      "alert_test": begin
        // do nothing
      end
      "exec_regwen": begin
        // do nothing
      end
      "exec": begin
        if (addr_phase_write) begin
          #1;
          detected_csr_exec = item.a_data;
        end
      end
      "status": begin
        if (addr_phase_read) begin
          void'(ral.status.predict(.value(exp_status), .kind(UVM_PREDICT_READ)));
        end
      end
      "ctrl_regwen": begin
        // do nothing
      end
      "ctrl": begin
        // do nothing if 0 is written
        if (addr_phase_write) begin
          if (item.a_data[SramCtrlRenewScrKey]) begin
            in_key_req = 1;
            exp_status[SramCtrlScrKeyValid] = 0;
            `uvm_info(`gfn, "raised in_key_req", UVM_HIGH)
          end
          if (item.a_data[SramCtrlInit]) begin
            in_init = 1;
            `uvm_info(`gfn, "raised in_init", UVM_HIGH)
          end
          if (in_key_req || in_init) exp_mem[cfg.sram_ral_name].init();
        end else if (addr_phase_read) begin
          // CTRL.renew_scr_key always reads as 0
          void'(ral.ctrl.renew_scr_key.predict(.value(0), .kind(UVM_PREDICT_READ)));

          // CTRL.init will be set to 0 once initialization is complete
          void'(ral.ctrl.init.predict(.value(in_init), .kind(UVM_PREDICT_READ)));
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
    key = sram_ctrl_pkg::RndCnstSramKeyDefault;
    nonce = sram_ctrl_pkg::RndCnstSramNonceDefault;
    mem_bkdr_scb.update_key(key, nonce);
    clear_hazard_state();
    exp_status = '0;
    handling_lc_esc = 0;
    status_lc_esc = 0;
    detected_csr_exec = '0;
    detected_hw_debug_en = '0;
    detected_en_sram_ifetch = '0;
    write_item_q.delete();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, sram_tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, sram_tl_d_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(push_pull_item#(.DeviceDataWidth(KDI_DATA_SIZE)), kdi_fifo)
    `DV_CHECK_EQ(write_item_q.size, 0)
    // check addr_phase_mbox
    while (addr_phase_mbox.num() != 0) begin
      sram_trans_t t;
      void'(addr_phase_mbox.try_get(t));
      `uvm_error(`gfn, $sformatf("addr_phase_mbox item uncompared:\n%0p", t))
    end

    // check completed_trans_mbox
    while (completed_trans_mbox.num() != 0) begin
      sram_trans_t t;
      void'(completed_trans_mbox.try_get(t));
      `uvm_error(`gfn, $sformatf("completed_trans_mbox item uncompared:\n%0p", t))
    end
  endfunction

endclass
