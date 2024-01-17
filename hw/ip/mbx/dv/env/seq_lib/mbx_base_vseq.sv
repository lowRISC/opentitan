// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
  The body of this base_vseq exercises the DUT by creating a number of 'transactions', which
  nominally involve the requester posting a message, the responder receiving this message then
  replying with its own message in return. Each transaction is a sequential series of operations,
  with hooks which optionally may insert 'stressors' (SOC_ABORT, ERROR, ROT_ABORT) which causes
  the nominal control flow to short-circuit to the end of the txn, while confirming we see the
  effect of these stressors.
  Each 'iteration' (num_iters) consists of a number of 'transactions' (num_txns), with a DUT reset
  seperating each iteration. This allows the regwen features to be meaningfully exercised.
  This is a quick, minimal effort extension of the existing 'smoke' test into something that more
  thoroughly exercises the mailbox IP at block level, including exceptional traffic/conditions.
  The linear-nature of stimulus->checking means it is not the basis of a proper DV stress test.
*/

class mbx_base_vseq extends cip_base_vseq #(
    .RAL_T               (mbx_core_reg_block),
    .CFG_T               (mbx_env_cfg),
    .COV_T               (mbx_env_cov),
    .VIRTUAL_SEQUENCER_T (mbx_virtual_sequencer)
  );

  `uvm_object_utils(mbx_base_vseq)

  string mbx_mem_ral_name = "mbx_mem_reg_block";
  string mbx_soc_ral_name = "mbx_soc_reg_block";

  // Number of iterations
  rand int unsigned num_iters;
  // Number of transactions (per iteration)
  // (sequential message transfers without an intervening DUT reset)
  rand int unsigned num_txns;

  mem_model seq_mem_model;

  mbx_tl_device_seq seq_h;

  mbx_mem_reg_block m_mbx_mem_ral;
  mbx_soc_reg_block m_mbx_soc_ral;

  mbx_seq_item mbx_config;
  bit p_expect_error = 1'b0; // Predictor variable

  // Number of words of memory available to the mailbox(es)
  int unsigned mbx_mem_words = 'h400;

  // Raise an Abort request from the SoC side?
  // Note: `aborted` shall already be clear, and be set here only when a new stimulus is applied.
  virtual task do_abort(ref bit aborted);
  endtask
  // Raise an Error from the Core side?
  // Note: `errored` shall already be clear, and be set here only when a new stimulus is applied.
  virtual task do_error(ref bit errored);
  endtask
  // Raise a FW-initiated Reset from the Core side?
  // Note: `panicked` shall already be clear, and be set here only when a new stimulus is applied.
  virtual task do_panic(ref bit panicked);
  endtask

  // Apply stressors to DUT?
  // Note: each of `aborted`, `errored` and `panicked` shall already be clear, and be set here only
  //       when a new stimulus is applied.
  virtual task stressors(ref bit aborted, ref bit errored, ref bit panicked);
    do_abort(aborted);
    do_error(errored);
    do_panic(panicked);
  endtask

  // Decide upon the access delays for this transaction.
  virtual function bit choose_access_delays(output int min_acc_delay, output int max_acc_delay);
    min_acc_delay = 0;
    max_acc_delay = 0;
    // Do not modify them by default.
    return 1'b0;
  endfunction

  virtual function bit choose_response_delays(output int min_rsp_delay, output int max_rsp_delay);
    min_rsp_delay = 0;
    max_rsp_delay = 0;
    // Do not modify them by default.
    return 1'b0;
  endfunction

  function new(string name = "");
    super.new();
    mbx_config = mbx_seq_item::type_id::create("mbx_config");
    seq_mem_model = mem_model#()::type_id::create("seq_mem_model");
  endfunction: new

  function void pre_randomize();
    super.pre_randomize();
    `downcast(m_mbx_soc_ral, cfg.ral_models[cfg.mbx_soc_ral_name])
    `downcast(m_mbx_mem_ral, cfg.ral_models[cfg.mbx_mem_ral_name])
  endfunction: pre_randomize

  // Task: Simulate a clock delay
  virtual task delay(int num = 1);
    cfg.clk_rst_vif.wait_clks(num);
  endtask : delay

  // Set the minimum and maximum grant delays of the mailbox SRAM
  // TODO: this function was introduced to guarantee the desired values during bring up;
  // it may no longer be required.
  function void set_access_delays(int min, int max);
    cfg.m_tl_agent_cfgs[mbx_mem_ral_name].a_ready_delay_min = min;
    cfg.m_tl_agent_cfgs[mbx_mem_ral_name].a_ready_delay_max = max;

    cfg.m_tl_agent_cfgs[RAL_T::type_name].a_valid_delay_min = min;
    cfg.m_tl_agent_cfgs[RAL_T::type_name].a_valid_delay_max = max;

    cfg.m_tl_agent_cfgs[mbx_soc_ral_name].a_valid_delay_min = min;
    cfg.m_tl_agent_cfgs[mbx_soc_ral_name].a_valid_delay_max = max;
  endfunction

  // Set the minimum and maximum response delays of the mailbox SRAM
  // TODO: this function was introduced to guarantee the desired values during bring up;
  // it may no longer be required.
  function void set_response_delays(int min, int max);
    cfg.m_tl_agent_cfgs[mbx_mem_ral_name].use_seq_item_d_valid_delay = 1'b0;
    cfg.m_tl_agent_cfgs[mbx_mem_ral_name].d_valid_delay_min = min;
    cfg.m_tl_agent_cfgs[mbx_mem_ral_name].d_valid_delay_max = max;

    cfg.m_tl_agent_cfgs[RAL_T::type_name].d_ready_delay_min = min;
    cfg.m_tl_agent_cfgs[RAL_T::type_name].d_ready_delay_max = max;

    cfg.m_tl_agent_cfgs[mbx_soc_ral_name].d_ready_delay_min = min;
    cfg.m_tl_agent_cfgs[mbx_soc_ral_name].d_ready_delay_max = max;

    seq_h.min_rsp_delay = min;
    seq_h.max_rsp_delay = max;
  endfunction

  // Enable/disable errors on TL-UL buses with the given percentage probability/word
  function void enable_bus_errors(int pct);
    seq_h.d_error_pct = pct;
  endfunction

  virtual function void randomize_mbx_config();
    `DV_CHECK_RANDOMIZE_FATAL(mbx_config)
    `uvm_info(`gfn, $sformatf("MBX: Randomized a new transaction:%s",
                              mbx_config.convert2string()), UVM_HIGH)
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
  endtask: dut_init

  // Start a sequence that creates a memory_model on the 'mem' interface.
  virtual task start_mem_seq();
    seq_h = mbx_tl_device_seq::type_id::create("seq_h");
    seq_h.mem = seq_mem_model;
    fork
      seq_h.start(p_sequencer.tl_sequencer_hs[cfg.mbx_mem_ral_name]);
    join_none
  endtask: start_mem_seq

  virtual task set_mem_range_regwen(mubi4_t regwen);
    `uvm_info(`gfn, $sformatf("Setting memory range regwen to 0x%x", regwen), UVM_MEDIUM)

    ral.address_range_regwen.regwen.set(int'(regwen));
    csr_update(ral.address_range_regwen);
  endtask

  virtual task set_address_range(mbx_addr_t ibmbx_base_addr, mbx_addr_t ibmbx_limit_addr,
                                 mbx_addr_t obmbx_base_addr, mbx_addr_t obmbx_limit_addr,
                                 bit range_valid, mubi4_t regwen);
    // Program the memory address ranges into the configuration registers
    csr_wr(ral.inbound_base_address,   ibmbx_base_addr);
    csr_wr(ral.inbound_limit_address,  ibmbx_limit_addr);
    csr_wr(ral.outbound_base_address,  obmbx_base_addr);
    csr_wr(ral.outbound_limit_address, obmbx_limit_addr);
    // Specify whether a valid range has been supplied
    csr_wr(ral.address_range_valid,    range_valid);
    // Set the lock as requested
    set_mem_range_regwen(regwen);
  endtask

  virtual task clear_mem();
    `uvm_info(`gfn, "Clearing memory", UVM_DEBUG)
    seq_mem_model.init();
  endtask

  virtual task write_mem(int start_addr, byte q[$]);
    `uvm_info(get_full_name(),
      $sformatf("write_mem(start_addr='h%0h, q=%p) -- Start", start_addr, q),
      UVM_DEBUG);
    foreach(q[ii]) begin
      seq_mem_model.write_byte((start_addr + ii), q[ii]);
    end
    `uvm_info(get_full_name(),
      $sformatf("write_mem(start_addr='h%0h, q=%p) -- End", start_addr, q),
      UVM_DEBUG);
  endtask: write_mem

  virtual task read_mem(int start_addr, int sz, ref byte q[$]);
    `uvm_info(get_full_name(),
      $sformatf("read_mem(start_addr='h%0h, sz=%0d) -- Start", start_addr, sz),
      UVM_DEBUG)
    q = {};
    for(int ii = 0; ii < sz; ii++) begin
      q[ii] = seq_mem_model.read_byte(start_addr + ii);
    end
    `uvm_info(get_full_name(),
      $sformatf("read_mem(start_addr='h%0h', sz=%0d, q=%p) -- Start", start_addr, sz, q),
      UVM_DEBUG)
  endtask: read_mem

  virtual task mbx_init();
    uvm_status_e status;

    `uvm_info(get_full_name(),
      $sformatf("mbx_init -- Start"),
      UVM_DEBUG)

    randomize_mbx_config();

    `uvm_info(get_full_name(),
      $sformatf("mbx_init -- End"),
      UVM_DEBUG)
  endtask: mbx_init

  virtual task mbx_abort();
    `uvm_info(`gfn, "ABORTing operation", UVM_HIGH)
    m_mbx_soc_ral.soc_control.go.set(1'b0);
    m_mbx_soc_ral.soc_control.abort.set(1'b1);
    csr_update(m_mbx_soc_ral.soc_control);
  endtask

  virtual task wait_for_core_interrupt(ref bit intr_ready, ref bit intr_abort,
                                       input int clks_timeout = 'h10000);
    bit aborted = 1'b0;
    `uvm_info(`gfn, $sformatf("wait_for_core_interrupt -- Start"), UVM_DEBUG)
    fork begin : iso_fork
      fork
        begin
          `DV_WAIT(cfg.intr_vif.pins[MbxCoreReady] == 1'b1, "core ready interrupt wait timeout")
        end
        begin
          `DV_WAIT(cfg.intr_vif.pins[MbxCoreAbort] == 1'b1, "core abort interrupt wait timeout")
          aborted = 1'b1;
        end
        begin
          cfg.clk_rst_vif.wait_clks(clks_timeout);
          `dv_fatal($sformatf("Timed out after %d clocks waiting for a core interrupt",
              clks_timeout), `gfn)
        end
      join_any;
      disable fork;
    end: iso_fork join
    if (aborted) begin
      intr_abort = 1'b1;
    end else begin
      intr_ready = 1'b1;
    end
    `uvm_info(`gfn, $sformatf("wait_for_core_interrupt -- End"), UVM_DEBUG)
  endtask : wait_for_core_interrupt

  virtual task wait_for_soc_interrupt(int clks_timeout = 'h10000);
    `uvm_info(`gfn, $sformatf("wait_for_soc_interrupt -- Start"), UVM_DEBUG)
    fork begin : iso_fork
      fork
        begin
          `DV_WAIT(cfg.intr_soc_vif.pins[0] == 1'b1, "soc interrupt wait timeout")
        end
        begin
          cfg.clk_rst_vif.wait_clks(clks_timeout);
          `dv_fatal($sformatf("Timed out after %d clocks waiting for a soc interrupt",
              clks_timeout), `gfn)
        end
      join_any;
      disable fork;
    end: iso_fork join
    `uvm_info(`gfn, $sformatf("wait_for_soc_interrupt -- End"), UVM_DEBUG)
  endtask : wait_for_soc_interrupt

  // Wait until the Ready/Abort interrupt is received on the Core side, or alternatively rely
  // upon the INTR_STATE register and polling.
  // If we decide to perform a FW-initiated reset ('panic') then neither will occur.
  task automatic wait_for_core_signal(output bit intr_ready,
                                      output bit intr_abort,
                                      output bit aborted,
                                      output bit errored,
                                      output bit panicked,
                                      input  bit intr_driven);
    // Detected interrupt/status bits on Core side
    bit got_ready = 1'b0;
    bit got_abort = 1'b0;
    // Generated stimuli
    bit gen_abort = 1'b0;
    bit gen_error = 1'b0;
    bit gen_panic = 1'b0;
    event e_stop;
    fork begin: iso_fork
      // With two processes we monitor CSR activity and interrupt signals concurrently.
      fork
        // CSR-driving thread generates errors and aborts as well as optionally polling the
        // INTR_STATE register.
        begin
          do begin
            // Ensure simulation time advances, even if this process has nothing to do!
            delay(1);
            stressors(gen_abort, gen_error, gen_panic);
            if (!intr_driven) begin
              bit [top_pkg::TL_DW-1:0] rd_data;
              csr_rd(ral.intr_state, rd_data);
              got_ready |= get_field_val(ral.intr_state.mbx_ready, rd_data);
              got_abort |= get_field_val(ral.intr_state.mbx_abort, rd_data);
            end
          end while (!(got_ready | got_abort | gen_error | gen_panic));
          // Signal to the parallel thread that the CSR registers are no longer being accessed.
          ->e_stop;
        end
        begin
          if (intr_driven) wait_for_core_interrupt(got_ready, got_abort);
            // Note: we must never kill the CSR-polling process because it may leave the RAL
            // locked, so this thread must only terminate with permission of the CSR process.
          wait (e_stop.triggered);
        end
      join_any
      // Ensure that the interrupt-monitoring process terminates.
      disable fork;
    end: iso_fork join
    // Signals from DUT
    intr_ready = got_ready;
    intr_abort = got_abort;
    // Generated stimuli
    aborted    = gen_abort;
    errored    = gen_error;
    panicked   = gen_panic;
  endtask

  virtual task body();
    `uvm_info(get_full_name(), "body -- Start", UVM_DEBUG)

    // Start a sequence that creates a memory_model on the 'mem' interface.
    start_mem_seq();

    // TODO: gross change to prevent explosions on accessing RDATA, since it does not behave like
    // a regular memory
    cfg.en_scb_mem_chk = 1'b0;

    for (int unsigned iter = 0; iter < num_iters; iter++) begin: b_num_iters
      `uvm_info(`gfn, $sformatf("Starting iteration %0d of %0d", iter + 1, num_iters), UVM_LOW)

      // Since the DUT has just been reset, we should take the opportunity to choose new memory
      // addresses.
      mbx_config.set_address_range_randomization(1'b1);

      // Initialize mailbox with randomized memory configuration.
      mbx_init();

      for (int unsigned txn = 0; txn < num_txns; txn++) begin
        bit [top_pkg::TL_DW-1:0] rd_data;
        bit [top_pkg::TL_DW-1:0] wr_data;
        int error_pct = $urandom_range(0, 200);
        bit intr_driven = $urandom & 1;
        bit check_request = 1'b0;
        bit send_response = 1'b0;
        int unsigned req_size_limit;
        int unsigned rsp_size_limit;
        int unsigned req_size;
        int unsigned rsp_size;
        bit panicked = 1'b0;
        bit errored = 1'b0;
        bit aborted = 1'b0;
        mbx_dword_t req[$];
        mbx_dword_t rsp[$];
        mbx_dword_t qd;
        bit obs_ready;
        bit obs_error;
        bit obs_busy;
        int min_rsp_delay;
        int max_rsp_delay;
        int min_acc_delay;
        int max_acc_delay;
        // TODO: whether to perform RDATA write accesses as blocking operations.
        bit rdata_wr_blocking = 1'b0;

        // TODO: perhaps we should change read_mem/write_mem to avoid issues.
        // The mailbox operates only on DWORD quantities.
        // mbx_dword_t q[$];
        byte q[$];

        // Empty the mailbox memory model of any previous contents.
        clear_mem();

        `uvm_info(`gfn, $sformatf("Starting transaction %0d of %0d", txn + 1, num_txns), UVM_LOW)

        // Generate a new configuration for the transaction.
        `DV_CHECK_RANDOMIZE_FATAL(mbx_config);

        // Generate a new configuration for the transaction.
        randomize_mbx_config();

        set_address_range(mbx_config.ibmbx_base_addr, mbx_config.ibmbx_limit_addr,
                          mbx_config.obmbx_base_addr, mbx_config.obmbx_limit_addr,
                          mbx_config.address_range_valid, mbx_config.address_range_regwen);

        // Enable/Disable Core interrupts.
        cfg_interrupts((1 << MbxCoreError) |
                       (1 << MbxCoreReady) |
                       (1 << MbxCoreAbort), intr_driven);
        `uvm_info(`gfn, $sformatf("Using interrupts? %s", intr_driven ? "Y" : "N"), UVM_MEDIUM)

        // Generate TL-UL bus errors during the operation.
        // TODO: this trips up the base scoreboard at present
        // enable_bus_errors((error_pct >= 100) ? 0 : error_pct);

        // Let the derived sequence vary the timing as appropriate; because of the back-pressuring
        // signals in DUT, there's a sequence that specifically sets 'zero_delays' to exercise
        // low latency bus responses.
        if (!cfg.zero_delays && choose_access_delays(min_acc_delay, max_acc_delay)) begin
          set_access_delays(min_acc_delay, max_acc_delay);
          `uvm_info(`gfn, $sformatf("Setting access delays [%d,%d]",
                                    min_acc_delay, max_acc_delay), UVM_MEDIUM)
        end
        if (!cfg.zero_delays && choose_response_delays(min_rsp_delay, max_rsp_delay)) begin
          set_response_delays(min_rsp_delay, max_rsp_delay);
          `uvm_info(`gfn, $sformatf("Setting response delays [%d,%d]",
                                    min_rsp_delay, max_rsp_delay), UVM_MEDIUM)
        end

        // ----------------------------------------------------------------------------------------
        // Request from SoC to RoT
        // ----------------------------------------------------------------------------------------

        // Data from R-code to ROT
        req_size = mbx_config.request_dwords;
        rsp_size = mbx_config.response_dwords;

        `uvm_info(`gfn, $sformatf("Request size 0x%x DWORD(s), Response size 0x%x DWORD(s)",
                                  req_size, rsp_size), UVM_MEDIUM)
        `uvm_info(`gfn,
                  $sformatf("Inbox should use address range [0x%x,0x%x]",
                            mbx_config.ibmbx_base_addr, mbx_config.ibmbx_base_addr + req_size * 4),
                  UVM_MEDIUM)
        `uvm_info(`gfn,
                  $sformatf("Outbox should use address range [0x%x,0x%x]",
                            mbx_config.obmbx_base_addr, mbx_config.obmbx_base_addr + rsp_size * 4),
                  UVM_MEDIUM)

        `uvm_info(`gfn, $sformatf("Constructing Request of 0x%0x DWORDs", req_size), UVM_MEDIUM)
        for(int unsigned ii = 0; ii < req_size; ii++) begin
          stressors(aborted, errored, panicked);

          if (aborted | panicked) begin
            if (!panicked) begin
              // We know that we're not permitted to write to WDATA whilst the mailbox is BUSY,
              // which should be expected if we've ABORTed the operation.
              uvm_reg_data_t data;
              csr_rd(m_mbx_soc_ral.soc_status, data);
              `DV_CHECK_EQ(get_field_val(m_mbx_soc_ral.soc_status.busy, data), 1'b1,
                           "SOC_STATUS.busy not set when expected in response to Abort request")
            end
            // Do NOT send the remainder of the Request.
            break;
          end else begin
            wr_data = $urandom();
            `uvm_info(`gfn, $sformatf(" - Offset 0x%0x : 0x%0x", ii, wr_data), UVM_HIGH)
            req.push_back(wr_data);
            tl_access(.addr(m_mbx_soc_ral.get_addr_from_offset(mbx_reg_pkg::MBX_WDATA_OFFSET)),
                      .write(1'b1), .data(wr_data), .mask(4'hF), .blocking(1'b1),
                      .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.mbx_soc_ral_name]));
          end
        end

        csr_rd(m_mbx_soc_ral.soc_status, rd_data);
        obs_error = get_field_val(m_mbx_soc_ral.soc_status.error, rd_data);

        if (!panicked & !aborted & !obs_error) begin
          // No disruption in the supply of the Request, activate the RoT
          bit intr_abort;
          bit intr_ready;

          // As we supplied all of the data, it should all make it into the mailbox SRAM.
          check_request = 1'b1;

          // Set the GO bit to mark complete transmission of the Request to the OT FW.
          m_mbx_soc_ral.soc_control.abort.set(1'b0);
          m_mbx_soc_ral.soc_control.go.set(1'b1);
          csr_update(m_mbx_soc_ral.soc_control);

          // Wait until the Ready interrupt is received on the Core side, or alternatively rely
          // upon the INTR_STATE register and polling.
          // If we decide to perform a FW-initiated reset ('panic') then neither will occur.
          wait_for_core_signal(intr_ready, intr_abort,      // Core side signals from DUT
                               aborted, errored, panicked,  // Stimuli generated by DV
                               intr_driven);                // Interrupt-driven operation?

          // Are we expecting the mailbox to be operational still?
          `uvm_info(`gfn, $sformatf("intr_ready %d abort %d errored %d panicked %d",
                                    intr_ready, intr_abort, errored, panicked), UVM_HIGH);
          send_response = intr_ready & !intr_abort & !aborted & !errored & !panicked;
        end

        if (check_request) begin
          // Collect the request message from the OT mailbox memory
          read_mem(mbx_config.ibmbx_base_addr, req_size << 2, q);

          for(int unsigned ii = 0; ii < req_size; ii++) begin
            qd = {q[ii*4+3],q[ii*4+2],q[ii*4+1],q[ii*4]};
            `uvm_info(`gfn, $sformatf("Expected Request DWORD %0h got %0h", req[ii], qd), UVM_HIGH)
            if (qd !== req[ii]) begin
              `uvm_error(`gfn,
                         $sformatf("Request DWORD mismatches q[%0d]('h%0h) != req[%0d]('h%0h)",
                                   ii, qd, ii, req[ii]))
            end
          end
          `uvm_info(`gfn, "Request data matched expectations", UVM_MEDIUM)
        end

        if (send_response) begin: b_send_response
          // Data from ROT to R-code
          q.delete();
          `uvm_info(`gfn, $sformatf("Constructing Response of 0x%0x DWORDs", rsp_size), UVM_MEDIUM)
          for(int unsigned ii = 0 ; ii < rsp_size; ii++) begin
            mbx_dword_t data = $urandom;
            `uvm_info(`gfn, $sformatf(" - Offset 0x%0x : 0x%0x", ii, data), UVM_HIGH)
             // TODO: replace this byte queue with DWORDs
            q.push_back(data[7:0]);
            q.push_back(data[15:8]);
            q.push_back(data[23:16]);
            q.push_back(data[31:24]);
          end

          // --------------------------------------------------------------------------------------
          // Response from RoT to SoC
          // --------------------------------------------------------------------------------------

          write_mem(mbx_config.obmbx_base_addr, q);
          // Writing to 'outbound_object_size' triggers the mbx to make the response available.
          csr_wr(ral.outbound_object_size, rsp_size);

          // Await assertion of READY bit or interrupt indicating that there's a Response available.
          do begin
            stressors(aborted, errored, panicked);

            csr_rd(m_mbx_soc_ral.soc_status, rd_data);
            `uvm_info(`gfn, $sformatf("rd_data for soc_status is :'h%0h", rd_data), UVM_DEBUG)

            // TODO: wait_soc_interrupt here
            // if intr_driven ...

            // We're waiting to see the READY bit, but we may also see BUSY in response to
            // an ABORT or ERROR if we raised an error.
            obs_error = get_field_val(m_mbx_soc_ral.soc_status.error, rd_data);
            obs_ready = get_field_val(m_mbx_soc_ral.soc_status.ready, rd_data);
          end while (!(aborted | panicked | obs_error | obs_ready));

          if (obs_ready & !aborted & !errored & !panicked) begin
            bit check_response = 1'b1;

            // Use an explicit termination signal for the other parallel thread, to avoid killing
            // it during a CSR access since doing so could leave the RAL locked.
            bit done = 1'b0;
            fork
              begin
                // Collect the entire message before checking it.
                // Note: this may not be the best approach unless we can time out in the event of a
                // lock up in the provision of new RDATA values.
                for(int unsigned ii = 0; ii < rsp_size && !done; ii++) begin
                  // Read from RDATA to collect the next message word
                  tl_access(.addr(cfg.ral.get_addr_from_offset(mbx_reg_pkg::MBX_RDATA_OFFSET)),
                            .write(1'b0), .data(rd_data), .mask(4'hF), .compare_mask(0),
                            .blocking(1'b1),
                            .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.mbx_soc_ral_name]));

                  `uvm_info(`gfn, $sformatf("Mailbox read data is : 'h%0h", rd_data), UVM_HIGH)

                  rsp.push_back(rd_data);

                  // Write anything to RDATA to advance to the next word.
                  wr_data = $urandom;
                  tl_access(.addr(cfg.ral.get_addr_from_offset(mbx_reg_pkg::MBX_RDATA_OFFSET)),
                            .write(1'b1), .data(wr_data), .mask(4'hF), .blocking(rdata_wr_blocking),
                            .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.mbx_soc_ral_name]));
                end
                `uvm_info(`gfn, "READ all DATA from SoC side", UVM_HIGH);
                done = 1'b1;
              end
              begin
                while (!done) begin
                  // Ensure simulation time advances, even if this process has nothing to do!
                  delay(1);
                  stressors(aborted, errored, panicked);

                  if (aborted | errored | panicked) begin
                    check_response = 1'b0;
                    done = 1'b1;
                  end
                end
                `uvm_info(`gfn, "Abort/Error process stopping", UVM_HIGH);
              end
            join

            if (check_response) begin
              for(int unsigned ii = 0; ii < rsp_size; ii++) begin
                qd = {q[ii*4+3],q[ii*4+2],q[ii*4+1],q[ii*4]};
                `uvm_info(`gfn,
                          $sformatf("Expected Response DWORD %0h got %0h", qd, rsp[ii]), UVM_HIGH)
                if (qd !== rsp[ii]) begin
                  `uvm_error(`gfn,
                             $sformatf("Response DWORD mismatches q[%0d]('h%0h) != rsp[%0d]('h%0h)",
                                       ii, qd, ii, rsp[ii]))
                end
              end
            end
          end
        end: b_send_response

        csr_rd(m_mbx_soc_ral.soc_status, rd_data);
        `uvm_info(`gfn, $sformatf("Transaction complete; SOC_STATUS 0x%0x", rd_data), UVM_MEDIUM)

        // Collect SoC.STATUS bits
        obs_busy  = get_field_val(m_mbx_soc_ral.soc_status.busy,  rd_data);
        obs_error = get_field_val(m_mbx_soc_ral.soc_status.error, rd_data);

        if (!p_expect_error) begin
          if (obs_error) `DV_CHECK_EQ(errored, 1'b1, "ERROR occurred, but not due to stressors!")
        end else if (p_expect_error && !obs_error && !(aborted || panicked)) begin
          // If we aborted/panicked, then even if the stimulus should have generated an error, we
          // won't see it.
          `uvm_error(`gfn, "Didn't observe an error when stimulus expected to generate one!")
        end
        p_expect_error = 1'b0;

         // Cleanup after error
        if (obs_error) begin
          `uvm_info(`gfn, "Clearing ERROR condition from SoC side using ABORT mechanism", UVM_HIGH)
          mbx_abort();
          aborted = 1'b1;

          // Check that the BUSY bit becomes set
          csr_rd(m_mbx_soc_ral.soc_status, rd_data);
          obs_busy  = get_field_val(m_mbx_soc_ral.soc_status.busy,  rd_data);
          obs_error = get_field_val(m_mbx_soc_ral.soc_status.error, rd_data);
          `DV_CHECK_EQ(obs_busy, 1'b1, "BUSY bit has not become set when ABORTing")
        end

        if (obs_busy) begin
          `DV_CHECK_EQ(aborted, 1'b1, "BUSY asserted but not ABORTed")

          // Abort occurred, clear it from the OT FW side
          `uvm_info(`gfn, "Clearing ABORT condition from OT FW side", UVM_HIGH)
          ral.control.abort.set(1'b1);
          ral.control.error.set(1'b0);  // Don't raise another ERROR!
          csr_update(ral.control);

          // Check that the BUSY bit resets
          csr_rd(m_mbx_soc_ral.soc_status, rd_data);
          obs_busy  = get_field_val(m_mbx_soc_ral.soc_status.busy,  rd_data);
          obs_error = get_field_val(m_mbx_soc_ral.soc_status.error, rd_data);
          `DV_CHECK_EQ(obs_busy, 1'b0, "BUSY bit cannot be cleared")
          `DV_CHECK_EQ(obs_error, 1'b0, "ERROR bit cannot be cleared")
        end

        `DV_CHECK_EQ(rd_data[31], 1'b0, "Ready bit still set")

        `uvm_info(`gfn, $sformatf("Completed transaction %0d of %0d", txn + 1, num_txns), UVM_LOW)

        // Ensure that we clear any asserted interrupts because otherwise they could interfere
        // with subsequent CSR-driven tests, in particular.
        csr_wr(ral.intr_state, (1 << MbxCoreError) |
                               (1 << MbxCoreReady) |
                               (1 << MbxCoreAbort));
        // Similarly control bits
        csr_wr(ral.control, 0);
        // SoC side interrupt
        m_mbx_soc_ral.soc_status.doe_intr_status.set(1'b1);
        csr_update(m_mbx_soc_ral.soc_status);

        // Can the memory range still be changed on subsequent transactions?
        if (mbx_config.address_range_regwen != MuBi4True) begin
          // Further changes are not expected to work until an IP reset, and the DV values must
          // remain in step with those used by the DUT.
          mbx_config.set_address_range_randomization(1'b0);
        end
      end: b_num_txns

      apply_resets_concurrently();
      delay(10);
    end: b_num_iters

    `uvm_info(get_full_name(), "body -- End", UVM_DEBUG)
  endtask : body

endclass : mbx_base_vseq
