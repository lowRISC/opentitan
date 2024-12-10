// Copyright lowRISC contributors (OpenTitan project).
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
  mubi4_t exp_scr_key_rotated = MuBi4False;

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

  // this bit is set after processing a KDI transaction and is used in the status CSR
  // comparison to detect mismatches due to random CDC delays.
  bit new_key_received = 0;
  // this bit is set after processing an init request transaction and is used in the status CSR
  // comparison to detect mismatches due to random CDC delays.
  bit init_after_new_key = 0;

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

    // Determine expected data.
    // When the access target was a CSR, tlul_adapter_reg always returns a '1.
    // When the access target was the memory, tlul_adapter_sram either returns
    // DataWhenInstrError ('1) or DataWhenError ('0) depending whether it was a
    // instruction type access or not.
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      exp_data = '1;
    end else begin
      // if error occurs when it's an instruction, return all 0 since it's an illegal instruction
      if (a_user.instr_type == prim_mubi_pkg::MuBi4True) exp_data = 0;
      else                                               exp_data = '1;
    end

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
      `RUN_FOREVR_W_RESET_EXIT(process_key_request)
      `RUN_FOREVR_W_RESET_EXIT(process_sram_init)
      `RUN_FOREVR_W_RESET_EXIT(process_lc_escalation)
      process_kdi_fifo();
      `RUN_FOREVR_W_RESET_EXIT(process_write_done_and_check)
    join_none
  endtask

  // write usually completes in a few cycles after TL address phase, but it may take longer time
  // when it's partial write or when RAW hazard occurs. It's not easy to know when it actually
  // finishes, so probe internal write_i instead
  task process_write_done_and_check();
    forever begin
      bit write_en;
      mem_item_t item;
      bit [AddrWidth-1:0] encrypt_addr;
      bit [TL_AW-1:0] decrypt_addr;

      wait (write_item_q.size > 0 || cfg.in_init);

      if (cfg.in_init) begin
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

      mem_bkdr_scb.write_finish(decrypt_addr, item.mask, !cfg.is_fi_test, !cfg.is_fi_test);
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
      @(posedge cfg.in_key_req);
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
          @(negedge cfg.in_key_req);
      )
    end
  endtask

  virtual task process_key_request();
    // Key requests happens once at the beginning of each simulation and whenever
    // CTRL.renew_scr_key CSR is written.
    forever begin
      @(posedge cfg.in_key_req);
      `uvm_info(`gfn, "Got cfg.in_key_req", UVM_MEDIUM)
      // Clear the scr key valid expectation, and wipe out the contents of CIP exp_mem since
      // all contents will change with new key/nonces.
      exp_status[SramCtrlScrKeyValid] = 0;
      exp_mem[cfg.sram_ral_name].init();

      if (cfg.under_reset) return;

      // Create expected response from kdi push_pull agent.
      begin
        otp_ctrl_pkg::sram_otp_key_rsp_t otp_rsp;
        `DV_CHECK_STD_RANDOMIZE_FATAL(otp_rsp)
        otp_rsp.ack = 1'b1;
        `uvm_info(`gfn, $sformatf("Adding d_user_data %p", otp_rsp), UVM_MEDIUM)
        cfg.m_kdi_cfg.add_d_user_data(otp_rsp);
      end
    end
  endtask

  virtual task process_sram_init();
    // SRAM initialization happens once at the beginning of each simulation and whenever
    // CTRL.init CSR is written. It requires a key to be provisioned from OTP first.
    // As a result we simply just wait for the first key request to end, and then wait for each line
    // of the memory to be written.
    forever begin
      @(posedge cfg.in_init);
      `uvm_info(`gfn, "Got cfg.in_init", UVM_MEDIUM)
      // clear the init done signal
      exp_status[SramCtrlInitDone] = 0;
      // add a small delay as in_key_req changes at the same time as in_init.
      #1;
      // Handle renew_scr_key.
      if (cfg.in_key_req) begin
        `DV_SPINWAIT(wait (cfg.in_key_req == 0);)
      end
      // Initialization process only starts once the corresponding key request finishes.
      // Initialization process will randomize each line in the SRAM, one cycle each
      // thus we just need to wait for a number of cycles equal to the total size
      // of the sram address space.
      `uvm_info(`gfn, "starting to wait for init", UVM_MEDIUM)
      // This gets interrupted by reset.
      `DV_SPINWAIT_EXIT(
          cfg.clk_rst_vif.wait_clks(cfg.mem_bkdr_util_h.get_depth());,
          wait (cfg.under_reset == 1'b1);,
          "Stopped waiting for ram init due to reset")
      if (cfg.under_reset) return;

      // If we are in escalated state, init_done will stay low.
      if (status_lc_esc == EscNone) begin
        // To determine the real end of memory initialization check status.init_done.
        csr_spinwait(.ptr(ral.status.init_done), .exp_data(1), .backdoor(1));
        exp_status[SramCtrlInitDone] = 1;
        // And flush the cip_scoreboard exp_mem since their contents are invalid.
        `uvm_info(`gfn, $sformatf("Initializing %s memory model", cfg.sram_ral_name), UVM_MEDIUM)
        exp_mem[cfg.sram_ral_name].init();
      end else begin
        exp_status[SramCtrlInitDone] = 0;
      end
      cfg.in_init = 0;
      init_after_new_key = 1;
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
      exp_scr_key_rotated = MuBi4False;

      // escalation resets the key and nonce back to defaults
      reset_key_nonce();

      // lc escalation status will be dropped after reset, no further action needed
      wait(cfg.lc_vif.lc_esc_en == lc_ctrl_pkg::Off);

      // there could be up to 7 transactions accepted but not compared due to escalation
      // 2 transactions are due to outstanding, allow another 6 pending items in the queue
      // as we skip checking them when lc_esc happens, and one more because of CDC delay
      // for lc_escalate_en_i
      `DV_CHECK_LE(mem_bkdr_scb.read_item_q.size + mem_bkdr_scb.write_item_q.size, 7)

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
      `DV_CHECK_EQ(cfg.in_key_req, 0, "No item is accepted during key req")
      `DV_CHECK_EQ(cfg.in_init, 0, "No item is accepted during init")
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

    `DV_CHECK_EQ(cfg.in_key_req, 0, "No item is accepted during key req")
    `DV_CHECK_EQ(cfg.in_init, 0, "No item is accepted during init")

    if (status_lc_esc == EscNone && !item.is_write()) begin
      mem_bkdr_scb.read_finish(item.d_data, simplify_addr(item.a_addr),
                               item.a_mask, !cfg.is_fi_test, !cfg.is_fi_test);
    end
  endtask

  // This task polls the kdi_fifo for completed key request transactions
  virtual task process_kdi_fifo();
    bit seed_valid;
    push_pull_item #(.DeviceDataWidth(KDI_DATA_SIZE)) item;
    forever begin
      kdi_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received transaction from kdi_fifo:\n%0s", item.convert2string()),
                UVM_MEDIUM)

      // after a KDI transaction is completed, it takes 3 clock cycles in the SRAM domain
      // to properly synchronize and propagate the data through the DUT
      cfg.clk_rst_vif.wait_clks(KDI_PROPAGATION_CYCLES);

      // To determine the real end of key processing check status.scr_key_valid.
      if (status_lc_esc == EscNone) begin
        csr_spinwait(.ptr(ral.status.scr_key_valid), .exp_data(1), .backdoor(1));
      end
      cfg.in_key_req = 0;
      if (!cfg.under_reset) begin
        // When KDI item is seen, update key, nonce
        `uvm_info(`gfn, $sformatf(
                  "mem_bkdr_scb.update_key with key=0x%x, nonce=0x%x, seed_valid=%0d",
                  key, nonce, seed_valid),
                  UVM_MEDIUM)
        if (status_lc_esc == EscNone) begin
          {key, nonce, seed_valid} = item.d_data;
          mem_bkdr_scb.update_key(key, nonce);

          // The scr_key_rotated and status.scr_key_valid will be updated.
          `uvm_info(`gfn, "Setting scr_key_rotated and scr_key_valid", UVM_MEDIUM)
          exp_scr_key_rotated = MuBi4True;
          exp_status[SramCtrlScrKeyValid]     = 1;
          exp_status[SramCtrlScrKeySeedValid] = seed_valid;
        end
      end
      // sample coverage on seed_valid
      if (cfg.en_cov) begin
        cov.key_seed_valid_cg.sample(status_lc_esc == EscFinal, seed_valid);
      end

      `uvm_info(`gfn, $sformatf("Updated key: 0x%0x", key), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("Updated nonce: 0x%0x", nonce), UVM_MEDIUM)

      // this is used by status CSR read checks.
      new_key_received = 1;
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    string  csr_name;
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

    csr_name = csr.get_name();
    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      // This is a W1C register and we need to update the expected value that we use in the
      // scoreboard if this register is written - otherwise this can lead to read mismatches
      // later down the road since we're going to use the wrong value for prediction.
      if ("scr_key_rotated" == csr_name && item.a_mask[0]) begin
        exp_scr_key_rotated = prim_mubi_pkg::mubi4_and_hi(exp_scr_key_rotated,
                                                          mubi4_t'(~item.a_data[3:0]));
        `uvm_info(`gfn, $sformatf("Updating expected src_key_rotated to 0x%x", exp_scr_key_rotated),
                  UVM_MEDIUM)
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr_name)
      // add individual case item for each csr
      "alert_test": begin
        if (addr_phase_write && item.a_data[0]) begin
          // Allow up to 10 cycles delay to consider a potential delay introduced
          // by enabling/disabling the SRAM readback feature during the test.
          set_exp_alert("fatal_error", .is_fatal(0), .max_delay(10));
        end
      end
      "exec_regwen": begin
        // do nothing
      end
      "exec": begin
        // do nothing
      end
      "readback_regwen": begin
        // do nothing
      end
      "readback": begin
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
          `uvm_info(`gfn, $sformatf("Updating ctrl CSR with 0x%x", item.a_data), UVM_MEDIUM)
          // Writes are blocked if regwen blocks them, and for renew_scr_key, if
          // status.scr_key_valid is 0.
          if (item.a_data[SramCtrlRenewScrKey] && `gmv(ral.ctrl_regwen) &&
              (`gmv(ral.status.scr_key_valid) == 0)) begin
            // Set cfg.in_key_req, and its side-effects are handled
            // in process_key_request.
            cfg.in_key_req = 1'b1;
            void'(ral.status.scr_key_valid.predict(.value(0), .kind(UVM_PREDICT_READ)));
          end
          if (item.a_data[SramCtrlInit] && `gmv(ral.ctrl_regwen)) begin
            // The side-effects of setting cfg.in_init are handled in process_sram_init.
            cfg.in_init = 1'b1;
            void'(ral.status.init_done.predict(.value(0), .kind(UVM_PREDICT_READ)));
          end
        end else if (addr_phase_read) begin
          // CTRL.renew_scr_key and CTRL.init always read as 0
          void'(ral.ctrl.renew_scr_key.predict(.value(0), .kind(UVM_PREDICT_READ)));
          void'(ral.ctrl.init.predict(.value(0), .kind(UVM_PREDICT_READ)));
        end
      end
      "scr_key_rotated": begin
        if (addr_phase_read) begin
          void'(ral.scr_key_rotated.predict(.value(exp_scr_key_rotated), .kind(UVM_PREDICT_READ)));
        end
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        // Some read mismatches may be due to CDC instrumentation that inserts a random delay in
        // synchronizers. In such cases, we allow for one mismatch here, but expect values to
        // stabilize by the next access.
        bit [TL_DW-1:0] mirrored_value = csr.get_mirrored_value();
        if (csr.get_name() == "status" && new_key_received && (
            mirrored_value[SramCtrlScrKeyValid] !=
            item.d_data[SramCtrlScrKeyValid] ||
            mirrored_value[SramCtrlScrKeySeedValid] !=
            item.d_data[SramCtrlScrKeySeedValid])) begin
          new_key_received = 0;
        end else if (csr.get_name() == "scr_key_rotated" && new_key_received && (
            mirrored_value != item.d_data)) begin
          new_key_received = 0;
        end else if (csr.get_name() == "status" && init_after_new_key &&
            mirrored_value[SramCtrlInitDone] !=
            item.d_data[SramCtrlInitDone]) begin
          init_after_new_key = 0;
        end else begin
          `DV_CHECK_EQ(mirrored_value, item.d_data,
                       $sformatf("reg name: %0s", csr.get_full_name()))
        end
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset_key_nonce();
    key = sram_ctrl_pkg::RndCnstSramKeyDefault;
    nonce = sram_ctrl_pkg::RndCnstSramNonceDefault;
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);

    reset_key_nonce();
    cfg.in_init = 0;
    cfg.in_key_req = 0;
    cfg.m_kdi_cfg.clear_d_user_data();
    new_key_received = 0;
    init_after_new_key = 0;
    mem_bkdr_scb.reset();
    `uvm_info(`gfn, $sformatf("mem_bkdr_scb.update_key with key=0x%x, nonce=0x%x", key, nonce),
              UVM_MEDIUM)
    mem_bkdr_scb.update_key(key, nonce);
    exp_status = '0;
    exp_scr_key_rotated = MuBi4False;
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
