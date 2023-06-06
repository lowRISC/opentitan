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

  // this bit is set to EscPending after lc_esc occurs, to signal that
  // the LC escalation may or may not be propagated to the design.
  // During EscPending, ignore checking data and d_error.
  // After we see d_error is set, we know LC escalation has finished propagating,
  // so set it to `EscFinal`.
  typedef enum {
    EscNone    = 0,
    EscPending = 1,
    EscFinal   = 2
  } lc_esc_status_type;
  lc_esc_status_type status_lc_esc;

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

  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(KDI_DATA_SIZE))) kdi_fifo;

  // local queues to hold incoming packets pending comparison

  otp_ctrl_pkg::sram_key_t key;
  otp_ctrl_pkg::sram_nonce_t nonce;

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

  // Check if the input tl_seq_item has any tl errors.
  //
  // NOTE: this function is designed to only work for tl_seq_item objects sent to the
  //       TLUL interface of the SRAM scrambling memory, as this interface does not
  //       care about CSR/uvm_mem addressing.
  //       For the same reason, we cannot use the already-provided `predict_tl_err(...)`
  //       function of the cip_base_scoreboard, as the SRAM TLUL interface does not have
  //       any CSRs or uvm_mems.
  virtual function bit get_sram_predict_tl_err(tl_seq_item item, tl_channels_e channel);
    bit is_tl_err;
    bit allow_ifetch;
    tlul_pkg::tl_a_user_t a_user       = tlul_pkg::tl_a_user_t'(item.a_user);
    prim_mubi_pkg::mubi8_t sram_ifetch = cfg.exec_vif.otp_en_sram_ifetch;
    lc_ctrl_pkg::lc_tx_t hw_debug_en   = cfg.exec_vif.lc_hw_debug_en;
    prim_mubi_pkg::mubi4_t  csr_exec   = prim_mubi_pkg::mubi4_t'(`gmv(ral.exec));

    if (cfg.en_cov) begin
      cov.executable_cg.sample(hw_debug_en,
                               sram_ifetch,
                               csr_exec);
    end
    if (`INSTR_EXEC) begin
      allow_ifetch = (sram_ifetch  == prim_mubi_pkg::MuBi8True) ?
                     (csr_exec == prim_mubi_pkg::MuBi4True)     :
                     (hw_debug_en == lc_ctrl_pkg::On);

    end else begin
      allow_ifetch = 0;
    end

    if (a_user.instr_type == prim_mubi_pkg::MuBi4True && item.a_opcode == tlul_pkg::Get) begin
      // 2 error cases (which lead to d_error = 1) if the InstrType is True:
      // - it is a write transaction (handled in cip_base_scoreboard::predict_tl_err, as it's a
      // common case for all blocks and that place also samples fcov.)
      // - the SRAM is not configured in executable mode (handled here, as it's a special case
      // for sram only)
      is_tl_err = !allow_ifetch;
    end

    if (status_lc_esc == EscPending && item.d_error) begin
      status_lc_esc = EscFinal;
    end
    if (status_lc_esc == EscFinal) is_tl_err |= 1;

    if (channel == DataChannel && is_tl_err) begin
      `DV_CHECK_EQ(item.d_error, 1,
          $sformatf({"item_err: %0d, allow_ifetch : %0d, sram_ifetch: %0d, exec: %0d, ",
                     "debug_en: %0d, lc_esc %0d"},
                    is_tl_err, allow_ifetch, sram_ifetch, csr_exec, hw_debug_en, status_lc_esc))
    end

    return is_tl_err;
  endfunction

  virtual function bit predict_tl_err(tl_seq_item item, tl_channels_e channel, string ral_name);
    if (ral_name == cfg.sram_ral_name && get_sram_predict_tl_err(item, channel)) begin
      return 1;
    end
    return super.predict_tl_err(item, channel, ral_name);
  endfunction

  virtual function void check_tl_read_value_after_error(tl_seq_item item, string ral_name);
    bit [TL_DW-1:0] exp_data;
    tlul_pkg::tl_a_user_t a_user = tlul_pkg::tl_a_user_t'(item.a_user);

    // if error occurs when it's an instrution, return all 0 since it's an illegal instruction
    if (a_user.instr_type == prim_mubi_pkg::MuBi4True) exp_data = 0;
    else                                               exp_data = '1;

    `DV_CHECK_EQ(item.d_data, exp_data, "d_data mismatch when d_error = 1")
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    kdi_fifo = new("kdi_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  `define RUN_FOREVR_W_RESET_EXIT(TASK) \
    forever begin \
      @(negedge cfg.under_reset); \
      `DV_SPINWAIT_EXIT(TASK();, \
                       @(posedge cfg.under_reset);) \
    end

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
    mem_bkdr_scb.en_cov = cfg.en_cov;

    super.run_phase(phase);
    fork
      `RUN_FOREVR_W_RESET_EXIT(sample_key_req_access_cg)
      `RUN_FOREVR_W_RESET_EXIT(process_sram_init)
      `RUN_FOREVR_W_RESET_EXIT(process_lc_escalation)
      process_kdi_fifo();
      `RUN_FOREVR_W_RESET_EXIT(process_write_done_and_check)
    join_none
  endtask

  // write usually completes in a few cycles after TL addrss phase, but it may take longer time
  // when it's partial write or when RAW hazard occurs. It's not easy to know when it actually
  // finishes, so probe internal write_i instead
  task process_write_done_and_check();
    forever begin
      bit write_en;
      mem_item_t item;
      bit [AddrWidth-1:0] encrypt_addr;
      bit [TL_AW-1:0] decrypt_addr;

      wait (write_item_q.size > 0 || in_init);

      if (in_init) begin
        // before entering init, there should be no pending write
        `DV_CHECK_EQ(write_item_q.size, 0)

        // init is to write init value to the sram, which will triggers 1<<AddrWidth write strobes
        // Below is to count all the strobe to make sure init is done, so that we know what strobe
        // is for the actual write
        repeat (1 << AddrWidth) wait_write_strobe();

        // One write may be accepted before init is done
        `DV_CHECK_LE(write_item_q.size, 1)
        continue;
      end
      item = write_item_q.pop_front();

      while (!write_en && status_lc_esc == EscNone) begin
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK(uvm_hdl_read(write_en_path, write_en))
      end
      if (status_lc_esc) continue;

      `DV_CHECK(uvm_hdl_read(write_addr_path, encrypt_addr))
      decrypt_addr = decrypt_sram_addr(encrypt_addr);
      decrypt_addr = decrypt_addr << 2;
      `uvm_info(`gfn, $sformatf("Write encrypt_addr 0x%0h, decrypt_addr 0x%0h",
                                encrypt_addr, decrypt_addr), UVM_MEDIUM)


      // the data should be settled after posedge. Wait for a 1ps to avoid race condition
      cfg.clk_rst_vif.wait_clks(1);
      #1ps;

      mem_bkdr_scb.write_finish(decrypt_addr, item.mask);
      `uvm_info(`gfn, $sformatf("Currently num of pending write items is %0d", write_item_q.size),
                UVM_MEDIUM)
    end
  endtask

  task wait_write_strobe();
    bit write_en;
    while (!write_en) begin
      cfg.clk_rst_vif.wait_n_clks(1);
      `DV_CHECK(uvm_hdl_read(write_en_path, write_en))
    end
  endtask

  // This task spins forever and samples the appropriate covergroup whenever
  // in_key_req is high and a new valid addr_phase transaction is seen on the memory bus.
  virtual task sample_key_req_access_cg();
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
  endtask

  virtual task process_sram_init();
    // SRAM initialization happens once at the beginning of each simulation and requires a key to be
    // provisioned from OTP first.
    // As a result we simply just wait for the first key request to end, and then wait for each line
    // of the memory to be written.
    forever begin
      @(posedge in_init);
      `uvm_info(`gfn, "Got in_init", UVM_MEDIUM)
      // clear the init done signal
      exp_status[SramCtrlInitDone] = 0;
      // add a small deblay as in_key_req changes at the same time as in_init.
      #1;
      // initialization process only starts once the corresponding key request finishes
      `DV_SPINWAIT(wait (in_key_req == 0);)
      // initialization process will randomize each line in the SRAM, one cycle each
      //
      // thus we just need to wait for a number of cycles equal to the total size
      // of the sram address space
      `uvm_info(`gfn, "starting to wait for init", UVM_MEDIUM)
      cfg.clk_rst_vif.wait_clks(cfg.mem_bkdr_util_h.get_depth());
      // Wait a small delay to latch the updated CSR status
      #1;
      // if we are in escalated state, scr_key_seed_valid will always stay low. otherwise
      // we can set the init done flag here.
      exp_status[SramCtrlInitDone] = status_lc_esc != EscNone ? 0 : 1;
      in_init = 0;
      `uvm_info(`gfn, "dropped in_init", UVM_MEDIUM)
    end
  endtask

  virtual task process_lc_escalation();
    forever begin
      // any non-off value is treated as true
      wait(cfg.lc_vif.lc_esc_en != lc_ctrl_pkg::Off);
      `uvm_info(`gfn, "LC escalation request detected", UVM_MEDIUM)

      cfg.clk_rst_vif.wait_clks(1);

      // signal that the escalation may be propagated to the design.
      status_lc_esc = EscPending;

      // clear exp_mem, scramble is changed due to escalation.
      exp_mem[cfg.sram_ral_name].init();

      exp_status[SramCtrlEscalated]       = 1;
      exp_status[SramCtrlScrKeySeedValid] = 0;
      exp_status[SramCtrlScrKeyValid]     = 0;
      exp_status[SramCtrlInitDone]        = 0;

      // escalation resets the key and nonce back to defaults
      reset_key_nonce();

      // lc escalation status will be dropped after reset, no further action needed
      wait(cfg.lc_vif.lc_esc_en == lc_ctrl_pkg::Off);

      // there could be up to 6 transactions accepted but not compared due to escalation
      // 2 transactions are due to outstanding, allow another 4 pending items in the queue
      // as we skip checking them when lc_esc happens
      `DV_CHECK_LE(mem_bkdr_scb.read_item_q.size + mem_bkdr_scb.write_item_q.size, 6)

      // sample coverage
      if (cfg.en_cov) begin
        bit idle = (mem_bkdr_scb.read_item_q.size + mem_bkdr_scb.write_item_q.size == 0);
        cov.lc_escalation_idle_cg.sample(idle);
      end
    end
  endtask

  virtual task process_sram_tl_a_chan_item(tl_seq_item item);
    `uvm_info(`gfn, $sformatf("Received sram_tl_a_chan item:\n%0s", item.sprint()), UVM_HIGH)

    // when esc occurs, access can be finished immediately with d_error, even if key req or
    // init is ongoing.
    if (status_lc_esc == EscNone) begin
      `DV_CHECK_EQ(in_key_req, 0, "No item is accepted during key req")
      `DV_CHECK_EQ(in_init, 0, "No item is accepted during init")
      if (cfg.en_cov) cov.subword_access_cg.sample(item.is_write(), item.a_mask);
    end

    if (item.is_write()) begin
      mem_bkdr_scb.write_start(simplify_addr(item.a_addr), item.a_data, item.a_mask);

      write_item_q.push_back(mem_item_t'{simplify_addr(item.a_addr),
                                         item.a_data, item.a_mask});
    end else begin
      mem_bkdr_scb.read_start(simplify_addr(item.a_addr), item.a_mask);
    end

  endtask

  virtual task process_sram_tl_d_chan_item(tl_seq_item item);
    `uvm_info(`gfn, $sformatf("Received sram_tl_d_chan item:\n%0s", item.sprint()), UVM_HIGH)

    `DV_CHECK_EQ(in_key_req, 0, "No item is accepted during key req")
    `DV_CHECK_EQ(in_init, 0, "No item is accepted during init")

    if (status_lc_esc == EscNone && !item.is_write()) begin
      mem_bkdr_scb.read_finish(item.d_data, simplify_addr(item.a_addr), item.a_mask);
    end
  endtask

  // This task polls the kdi_fifo for completed key request transactions
  virtual task process_kdi_fifo();
    bit seed_valid;
    push_pull_item #(.DeviceDataWidth(KDI_DATA_SIZE)) item;
    forever begin
      kdi_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received transaction from kdi_fifo:\n%0s", item.convert2string()),
                UVM_HIGH)

      // after a KDI transaction is completed, it takes 3 clock cycles in the SRAM domain
      // to properly synchronize and propagate the data through the DUT
      cfg.clk_rst_vif.wait_clks(KDI_PROPAGATION_CYCLES);

      // Wait a small delay before updating CSR status
      #1;

      in_key_req = 0;
      `uvm_info(`gfn, "dropped in_key_req", UVM_MEDIUM)

      // When KDI item is seen, update key, nonce
      {key, nonce, seed_valid} = item.d_data;
      mem_bkdr_scb.update_key(key, nonce);

      // sample coverage on seed_valid
      if (cfg.en_cov) begin
        cov.key_seed_valid_cg.sample(status_lc_esc == EscFinal, seed_valid);
      end

      // if we are in escalated state, key_valid and scr_key_seed_valid will remain low
      if (status_lc_esc == EscNone) begin
        exp_status[SramCtrlScrKeyValid]     = 1;
        exp_status[SramCtrlScrKeySeedValid] = seed_valid;
      end

      `uvm_info(`gfn, $sformatf("Updated key: 0x%0x", key), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("Updated nonce: 0x%0x", nonce), UVM_MEDIUM)
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    if (ral_name == cfg.sram_ral_name) begin
      if (channel == AddrChannel) process_sram_tl_a_chan_item(item);
      else                        process_sram_tl_d_chan_item(item);
      return;
    end

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
        if (addr_phase_write && item.a_data[0]) set_exp_alert("fatal_error", .is_fatal(0));
      end
      "exec_regwen": begin
        // do nothing
      end
      "exec": begin
        // do nothing
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
          if (item.a_data[SramCtrlRenewScrKey] && `gmv(ral.ctrl_regwen)) begin
            in_key_req = 1;
            exp_status[SramCtrlScrKeyValid] = 0;
            `uvm_info(`gfn, "raised in_key_req", UVM_MEDIUM)
          end
          if (item.a_data[SramCtrlInit] && `gmv(ral.ctrl_regwen)) begin
            in_init = 1;
            `uvm_info(`gfn, "raised in_init", UVM_MEDIUM)
          end
          if (in_key_req || in_init) exp_mem[cfg.sram_ral_name].init();
        end else if (addr_phase_read) begin
          // CTRL.renew_scr_key and CTRL.init always read as 0
          void'(ral.ctrl.renew_scr_key.predict(.value(0), .kind(UVM_PREDICT_READ)));
          void'(ral.ctrl.init.predict(.value(0), .kind(UVM_PREDICT_READ)));
        end
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

  virtual function void reset_key_nonce();
    key = sram_ctrl_pkg::RndCnstSramKeyDefault;
    nonce = sram_ctrl_pkg::RndCnstSramNonceDefault;
  endfunction

  virtual function void reset(string kind = "HARD");
    sram_trans_t t;
    super.reset(kind);

    reset_key_nonce();
    in_init = 0;
    in_key_req = 0;
    mem_bkdr_scb.reset();
    mem_bkdr_scb.update_key(key, nonce);
    exp_status = '0;
    write_item_q.delete();
    exp_mem[cfg.sram_ral_name].init();

    // Once esc happens, vseq will send enough transaction to make sure d_error occurs
    // so that scb updates to EscFinal
    `DV_CHECK_NE(status_lc_esc, EscPending)
    status_lc_esc = EscNone;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(push_pull_item#(.DeviceDataWidth(KDI_DATA_SIZE)), kdi_fifo)
    `DV_CHECK_EQ(write_item_q.size, 0)
  endfunction

endclass
`undef RUN_FOREVR_W_RESET_EXIT
