// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
  // Number of transactions (message transfers within an iteration without an=
  // intervening DUT reset)
  rand int unsigned num_txns;

  mem_model seq_mem_model;

  mbx_tl_device_seq seq_h;

  mbx_mem_reg_block m_mbx_mem_ral;
  mbx_soc_reg_block m_mbx_soc_ral;

  mbx_seq_item mbx_config;

  // Number of words of memory available to the mailbox(es)
  int unsigned mbx_mem_words = 'h400;

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

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
  endtask: dut_init

  virtual task start_device_seq();
    seq_h = mbx_tl_device_seq::type_id::create("seq_h");
    seq_h.mem = seq_mem_model;
    fork
      seq_h.start(p_sequencer.tl_sequencer_hs[cfg.mbx_mem_ral_name]);
    join_none
  endtask: start_device_seq

  virtual task set_mem_range_regwen(mubi4_t regwen);
    `uvm_info(`gfn, $sformatf("Setting memory range regwen to 0x%x", regwen), UVM_LOW)

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

    `DV_CHECK_RANDOMIZE_FATAL(mbx_config)

    `uvm_info(get_full_name(),
      $sformatf("mbx_init -- End"),
      UVM_DEBUG)
  endtask: mbx_init

  virtual task wait_for_core_interrupt(int clks_timeout=1024);
    `uvm_info(`gfn, $sformatf("wait_for_core_interrupt -- Start"), UVM_DEBUG)
    fork begin : isolation_fork
      fork
        begin
          `DV_WAIT(cfg.intr_vif.pins[MbxCoreReady] == 1'b1, "core interrupt wait timeout")
        end
        begin
          cfg.clk_rst_vif.wait_clks(clks_timeout);
          `dv_fatal($sformatf("Timed out after %d clocks waiting for a core interrupt",
              clks_timeout), `gfn)
        end
      join_any;
      disable fork;
    end join
    `uvm_info(`gfn, $sformatf("wait_for_core_interrupt -- End"), UVM_DEBUG)
  endtask: wait_for_core_interrupt

  virtual task wait_for_soc_interrupt(int clks_timeout=1024);
    `uvm_info(`gfn, $sformatf("wait_for_soc_interrupt -- Start"), UVM_DEBUG)
    fork begin : isolation_fork
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
    end join
    `uvm_info(`gfn, $sformatf("wait_for_soc_interrupt -- End"), UVM_DEBUG)
  endtask: wait_for_soc_interrupt

  virtual task body();
    `uvm_info(get_full_name(), "body -- Start", UVM_DEBUG)
    start_device_seq();

    // TODO: gross change to prevent explosions on accessing RDATA, since it does not behave like
    // a regular memory
    cfg.en_scb_mem_chk = 1'b0;

    for (int unsigned iter = 0; iter < num_iters; iter++) begin
      `uvm_info(`gfn, $sformatf("Starting iteration %d of %d", iter + 1, num_iters), UVM_LOW)

      // Since the DUT has just been reset, we should take the opportunity to choose new memory
      // addresses.
      mbx_config.set_address_range_randomization(1'b1);

      // Initialize mailbox with randomized memory configuration.
      mbx_init();

      for (int unsigned txn = 0; txn < num_txns; txn++) begin
        bit [top_pkg::TL_DW-1:0] rd_data;
        bit [top_pkg::TL_DW-1:0] wr_data;
        bit intr_driven = 1'b1;  // TODO: support either CSR or interrupts.
        bit check_request = 1'b0;
        bit send_response = 1'b0;
        int unsigned req_size_limit;
        int unsigned rsp_size_limit;
        int unsigned req_size;
        int unsigned rsp_size;
        mbx_dword_t req[$];
        mbx_dword_t rsp[$];
        mbx_dword_t qd;
        bit obs_ready;
        bit obs_error;
        bit obs_busy;
        // TODO: whether to perform RDATA write accesses as blocking operations.
        bit rdata_wr_blocking = 1'b1;

        // TODO: perhaps we should change read_mem/write_mem to avoid issues.
        // The mailbox operates only on DWORD quantities.
        // mbx_dword_t q[$];
        byte q[$];

        // Empty the mailbox memory model of any previous contents.
        clear_mem();

        `uvm_info(`gfn, $sformatf("Starting transaction %d of %d", txn + 1, num_txns), UVM_LOW)

        set_address_range(mbx_config.ibmbx_base_addr, mbx_config.ibmbx_limit_addr,
                          mbx_config.obmbx_base_addr, mbx_config.obmbx_limit_addr,
                          mbx_config.address_range_valid, mbx_config.address_range_regwen);

        // Enable/Disable Core interrupts.
        cfg_interrupts((1 << MbxCoreError) |
                       (1 << MbxCoreReady) |
                       (1 << MbxCoreAbort), intr_driven);
        `uvm_info(`gfn, $sformatf("Using interrupts? %s", intr_driven ? "Y" : "N"), UVM_MEDIUM)

        // ----------------------------------------------------------------------------------------
        // Request from SoC to RoT
        // ----------------------------------------------------------------------------------------

        // Data from R-code to ROT
        req_size = mbx_config.request_dwords;
        rsp_size = mbx_config.response_dwords;

        `uvm_info(`gfn, $sformatf("Request size %x DWORD(s), Response size %x DWORD(s)",
                                  req_size, rsp_size), UVM_LOW)
        `uvm_info(`gfn,
                  $sformatf("Inbox should use address range [%x,%x)",
                            mbx_config.ibmbx_base_addr, mbx_config.ibmbx_base_addr + req_size * 4),
                  UVM_LOW)
        `uvm_info(`gfn,
                  $sformatf("Outbox should use address range [%x,%x)",
                            mbx_config.obmbx_base_addr, mbx_config.obmbx_base_addr + rsp_size * 4),
                  UVM_LOW)

        `uvm_info(`gfn, $sformatf("Constructing Request of 0x%0x DWORDs", req_size), UVM_LOW)
        for(int unsigned ii = 0; ii < req_size; ii++) begin
          wr_data = $urandom();
          `uvm_info(`gfn, $sformatf(" - Offset 0x%0x : 0x%0x", ii, wr_data), UVM_LOW)
          req.push_back(wr_data);
          tl_access(.addr(m_mbx_soc_ral.get_addr_from_offset(mbx_reg_pkg::MBX_WDATA_OFFSET)),
                    .write(1'b1), .data(wr_data), .mask(4'hF), .blocking(1'b1),
                    .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.mbx_soc_ral_name]));
        end

        csr_rd(m_mbx_soc_ral.soc_status, rd_data);
        // Set the GO bit to mark complete transmission of the Request to the OT FW.
        m_mbx_soc_ral.soc_control.abort.set(1'b0);
        m_mbx_soc_ral.soc_control.go.set(1'b1);
        csr_update(m_mbx_soc_ral.soc_control);

        wait_for_core_interrupt();
        clear_all_interrupts();

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
        `uvm_info(`gfn, "Request data matched expectations", UVM_LOW)

        // Data from ROT to R-code
        q.delete();
        `uvm_info(`gfn, $sformatf("Constructing Response of 0x%0x DWORDs", rsp_size), UVM_LOW)
        for(int unsigned ii = 0 ; ii < rsp_size; ii++) begin
          mbx_dword_t data = $urandom;
          `uvm_info(`gfn, $sformatf(" - Offset 0x%0x : 0x%0x", ii, data), UVM_LOW)
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
        csr_wr(ral.outbound_object_size, rsp_size);

        wait_for_soc_interrupt();
        csr_rd(m_mbx_soc_ral.soc_status, rd_data);
        `DV_CHECK_EQ(rd_data[31], 1'b1, "soc_status ready bit not set after soc interrupt seen")
        clear_all_interrupts();

        // Collect the entire message before checking it.
        // Note: this may not be the best approach unless we can time out in the event of a
        // lock up in the provision of new RDATA values.
        for(int unsigned ii = 0; ii < rsp_size; ii++) begin
          // Read from RDATA to collect the next message word
          tl_access(.addr(cfg.ral.get_addr_from_offset(mbx_reg_pkg::MBX_RDATA_OFFSET)),
                    .write(1'b0), .data(rd_data), .mask(4'hF), .compare_mask(0),
                    .blocking(1'b1),
                    .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.mbx_soc_ral_name]));

          `uvm_info(`gfn, $sformatf("Mailbox read data is : 'h%0h", rd_data), UVM_LOW)

          rsp.push_back(rd_data);

          // Write anything to RDATA to advance to the next word.
          wr_data = $urandom;
          tl_access(.addr(cfg.ral.get_addr_from_offset(mbx_reg_pkg::MBX_RDATA_OFFSET)),
                    .write(1'b1), .data(wr_data), .mask(4'hF), .blocking(rdata_wr_blocking),
                    .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.mbx_soc_ral_name]));
        end
        `uvm_info(`gfn, "READ all DATA from SoC side", UVM_HIGH);

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

        csr_rd(m_mbx_soc_ral.soc_status, rd_data);
        `uvm_info(`gfn, $sformatf("Transaction complete; SOC_STATUS 0x%0x", rd_data), UVM_MEDIUM)

        `DV_CHECK_EQ(rd_data[31], 1'b0, "Ready bit still set")

        `uvm_info(`gfn, $sformatf("Completing transaction %d of %d", txn + 1, num_txns), UVM_LOW)

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

        // Generate a new configuration for the next transaction, if there is one.
        `DV_CHECK_RANDOMIZE_FATAL(mbx_config);
      end

      apply_resets_concurrently();
      delay(10);
    end

    `uvm_info(get_full_name(), "body -- End", UVM_DEBUG)
  endtask : body

endclass : mbx_base_vseq
