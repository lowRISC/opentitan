// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_base_vseq #(
  type RAL_T = chip_ral_pkg::chip_reg_block
) extends cip_base_vseq #(
  .CFG_T              (chip_env_cfg),
  .RAL_T              (RAL_T),
  .COV_T              (chip_env_cov),
  .VIRTUAL_SEQUENCER_T(chip_virtual_sequencer)
);
  `uvm_object_utils(chip_base_vseq)

  jtag_dmi_reg_block jtag_dmi_ral;

  // Local queue for holding received UART TX data.
  byte uart_tx_data_q[$];

  // Indicates the first power up of the chip.
  bit is_first_pwrup = 1'b1;

  // Skip POR_N : required for closed source test
  bit skip_por_n_during_first_pwrup = 0;

  `uvm_object_new

  virtual function void set_handles();
    super.set_handles();
    jtag_dmi_ral = cfg.jtag_dmi_ral;
  endfunction // set_handles

  task post_start();
    do_clear_all_interrupts = 0;
    super.post_start();
  endtask

  virtual task apply_reset(string kind = "HARD");
    callback_vseq.pre_apply_reset();
    // Note: The JTAG reset does not have a dedicated pad and is muxed with other chip IOs.
    // These IOs have pad attributes that are driven from registers, and as long as
    // the reset line of those registers is X, the registers and hence the pad outputs
    // will also be X. This causes the JTAG reset to not properly propagate, and hence we
    // have to assert the main reset before that (release can happen in a randomized way
    // via the apply_reset task later on).
    // assert_por_reset();
    void'($value$plusargs("skip_por_n_during_first_pwrup=%0b", skip_por_n_during_first_pwrup));
    if (!(skip_por_n_during_first_pwrup && is_first_pwrup)) begin
      `uvm_info(`gfn, "Asserting POR_N", UVM_LOW)
      cfg.chip_vif.por_n_if.drive(0);
      #10us;  // TODO: revisit this.
      cfg.chip_vif.por_n_if.drive(1);
      `uvm_info(`gfn, "POR_N complete", UVM_LOW)
    end
    // TODO: Cannot assert different types of resets in parallel; due to randomization
    // resets de-assert at different times. If the main rst_n de-asserts before others,
    // the CPU starts executing right away which can cause breakages.
    cfg.m_jtag_riscv_agent_cfg.m_jtag_agent_cfg.vif.do_trst_n();
    super.apply_reset(kind);
    if (jtag_dmi_ral != null) jtag_dmi_ral.reset(kind);
    callback_vseq.post_apply_reset();
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.chip_vif.por_n_if.drive(0);
    // At least 6 AON clock cycles.
    // TODO: Tentatively this is set to 100us. Fetch the individual clock freqs from AST via
    // chip_vif.
    reset_duration_ps = max2(reset_duration_ps, 100_000_000 /* 100us */);
    super.apply_resets_concurrently(reset_duration_ps);
    cfg.chip_vif.por_n_if.drive(1);
  endtask

  chip_callback_vseq callback_vseq;

  // This task populates the ROM with random but correctly scrambled and ECC encoded data with a
  // valid KMAC digest at the end. It is used to ensure the ROM check can pass successfully, without
  // having to rely on a ROM software build prior to running the simulation.
  virtual function void random_rom_init_with_digest();
    bit [TL_DW-1:0] rnd_data;
    `uvm_info(`gfn, "Random ROM init with digest", UVM_MEDIUM)

    // Randomize the memory contents.
    //
    // We can't just use the mem_bkdr_util randomize_mem function because that doesn't obey the
    // scrambling key. This wouldn't be a problem (the memory is supposed to be random!), except
    // that we also need to pick ECC values that match.
    for (int addr = 0; addr < RomMaxCheckAddr; addr += TL_DW/8) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(rnd_data)
      cfg.mem_bkdr_util_h[Rom].rom_encrypt_write32_integ(
          addr,
          rnd_data,
          top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrKey,
          top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrNonce,
          1'b1); // Enable scrambling.
    end

    // Update the ROM digest.
    cfg.mem_bkdr_util_h[Rom].update_rom_digest(
        top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrKey,
        top_earlgrey_rnd_cnst_pkg::RndCnstRomCtrlScrNonce);
  endfunction

  // Iniitializes the DUT.
  //
  // Initializes DUT inputs, internal memories, etc., brings the DUT out of reset (performs a reset
  // cycle) and  performs immediate post-reset steps to prime the design for stimulus. The
  // base class method invoked by super.dut_init() applies the reset.
  virtual task dut_init(string reset_kind = "HARD");
    bit otp_clear_hw_cfg, otp_clear_secret0, otp_clear_secret1, otp_clear_secret2;
    // Connect the external clock source if the test needs it.
    //
    // TODO: This is a functional interface which should ideally be connected only in the extended
    // test sequences. Revisit this later.
    callback_vseq.pre_dut_init();
    if (cfg.chip_clock_source != ChipClockSourceInternal) begin
      `uvm_info(`gfn, {"Connecting and driving external clock source with frequency ",
                       $sformatf("%0dMhz", cfg.chip_clock_source)}, UVM_LOW)
      cfg.chip_vif.ext_clk_if.set_active(.drive_clk_val(1), .drive_rst_n_val(0));
      cfg.chip_vif.ext_clk_if.set_freq_mhz(cfg.chip_clock_source);
    end

    // Connect DIOs
    cfg.chip_vif.enable_spi_host = 1;

    // Initialize all memories via backdoor.
    cfg.mem_bkdr_util_h[FlashBank0Info].set_mem();
    cfg.mem_bkdr_util_h[FlashBank1Info].set_mem();
    // Backdoor load the OTP image.
    cfg.mem_bkdr_util_h[Otp].load_mem_from_file(cfg.otp_images[cfg.use_otp_image]);
    // Plusargs to selectively clear the provisioning state of some of the OTP partitions.
    // This is useful in tests that make front-door accesses for provisioning purposes.
    void'($value$plusargs("otp_clear_hw_cfg=%0d", otp_clear_hw_cfg));
    void'($value$plusargs("otp_clear_secret0=%0d", otp_clear_secret0));
    void'($value$plusargs("otp_clear_secret1=%0d", otp_clear_secret1));
    void'($value$plusargs("otp_clear_secret2=%0d", otp_clear_secret2));
    if (otp_clear_hw_cfg) begin
        cfg.mem_bkdr_util_h[Otp].otp_clear_hw_cfg_partition();
    end
    if (otp_clear_secret0) begin
        cfg.mem_bkdr_util_h[Otp].otp_clear_secret0_partition();
    end
    if (otp_clear_secret1) begin
        cfg.mem_bkdr_util_h[Otp].otp_clear_secret1_partition();
    end
    if (otp_clear_secret2) begin
        cfg.mem_bkdr_util_h[Otp].otp_clear_secret2_partition();
    end

    initialize_otp_sig_verify();
    initialize_otp_creator_sw_cfg_ast_cfg();
    // Initialize selected memories to all 0. This is required for some chip-level tests such as
    // otbn_mem_scramble that may intentionally read memories before writing them. Reading these
    // memories still triggeres ECC integrity errors that need to be handled by the test.
    cfg.mem_bkdr_util_h[OtbnImem].clear_mem();
    for (int ram_idx = 0; ram_idx < cfg.num_otbn_dmem_tiles; ram_idx++) begin
      cfg.mem_bkdr_util_h[chip_mem_e'(OtbnDmem0 + ram_idx)].clear_mem();
    end
    // Early cpu init
    if (cfg.early_cpu_init) cpu_init();
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
    alert_ping_en_shorten();
    callback_vseq.post_dut_init();

    // Clear once upon the chip exiting the first reset.
    is_first_pwrup = 0;
  endtask

  // Place holder for cpu_init task
  // initial implementation is in chip_sw_base_vseq.sv
  virtual task cpu_init();endtask

  virtual task dut_shutdown();
    // check for pending chip operations and wait for them to complete
    // TODO
  endtask

  virtual task wait_rom_check_done();
    // The CSR tests (handled by this class) need to wait until the lc_ctrl has initialized and
    // rom_ctrl block has finished running KMAC before they can start issuing reads and writes.
    // Otherwise, they might write to a KMAC register while KMAC is in operation, or access a
    // register that is gated by life cycle.
    // This would either generate an error or have no effect and a subsequent read
    // from the register would show a mismatched value. We handle this by considering rom_ctrl's
    // operation as "part of reset".
    // Same for the test that uses jtag to access CSRs. We need to wait until rom check is done.
    //
    // This function is meant to be called once the base class reset is finished.
    // Use backdoor, so that this task can be used with or without stub mode enabled.

    `uvm_info(`gfn, "waiting for rom_ctrl after reset", UVM_MEDIUM)
    csr_spinwait(.ptr(ral.rom_ctrl_regs.digest[0]), .exp_data(0), .compare_op(CompareOpNe),
                 .backdoor(1), .spinwait_delay_ns(1000));
    `uvm_info(`gfn, "rom_ctrl check done after reset", UVM_HIGH)
    csr_spinwait(.ptr(ral.lc_ctrl.status.ready), .exp_data(1), .backdoor(1),
                 .spinwait_delay_ns(1000));
    `uvm_info(`gfn, "lc_ctrl has been initialized", UVM_HIGH)
  endtask

  virtual task pre_start();
    // Do DUT init after some additional settings.
    bit do_dut_init_save = do_dut_init;
    do_dut_init = 1'b0;
    `uvm_create_on(callback_vseq, p_sequencer);
    `DV_CHECK_RANDOMIZE_FATAL(callback_vseq)
    super.pre_start();
    // Randomize the ROM image with valid ECC and digest. Subclasses that have an actual ROM image
    // will load a "real" ROM image later. If the ROM integrity check is disabled, no digest needs
    // to be calculated and we can just randomize the memory.
    `ifdef DISABLE_ROM_INTEGRITY_CHECK
      cfg.mem_bkdr_util_h[Rom].randomize_mem();
    `else
      random_rom_init_with_digest();
    `endif
    do_dut_init = do_dut_init_save;
    // Now safe to do DUT init.
    if (do_dut_init) dut_init();
  endtask

  // Configures and connects the UART agent for driving data over RX and receiving data on TX.
  //
  // Note that to fetch packets over the TX port, the get_uart_tx_items() task needs to be called
  // separately as a forked thread in the test sequence.
  //
  // uart_idx: The UART instance.
  // enable: 1: enable (configures and connects), 0: disable (disables sampling and disconnects)
  // enable_tx_monitor: Enable sampling data on the TX port (default on).
  // enable_rx_monitor: Enable sampling data on the RX port (default off).
  // en_parity: Enable parity when driving RX traffic.
  // odd_parity: Compute odd parity when driving RX traffic.
  // baud_rate: The baud rate.
  virtual function void configure_uart_agent(int uart_idx,
                                             bit enable,
                                             bit enable_tx_monitor = 1'b1,
                                             bit enable_rx_monitor = 1'b0,
                                             bit en_parity = 1'b0,
                                             bit odd_parity = 1'b0,
                                             baud_rate_e baud_rate = cfg.uart_baud_rate);
    if (enable) begin
      `uvm_info(`gfn, $sformatf("Configuring and connecting UART%0d", uart_idx), UVM_LOW)
      cfg.m_uart_agent_cfgs[uart_idx].set_parity(en_parity, odd_parity);
      cfg.m_uart_agent_cfgs[uart_idx].set_baud_rate(cfg.uart_baud_rate);
      cfg.m_uart_agent_cfgs[uart_idx].en_tx_monitor = enable_tx_monitor;
      cfg.m_uart_agent_cfgs[uart_idx].en_rx_monitor = enable_rx_monitor;
      cfg.chip_vif.enable_uart(uart_idx, 1);
    end else begin
      `uvm_info(`gfn, $sformatf("Disconnecting UART%0d", uart_idx), UVM_LOW)
      cfg.m_uart_agent_cfgs[uart_idx].en_tx_monitor = 0;
      cfg.m_uart_agent_cfgs[uart_idx].en_rx_monitor = 0;
      cfg.chip_vif.enable_uart(uart_idx, 0);
    end
  endfunction

  // Grab packets sent by the DUT over the UART TX port.
  virtual task get_uart_tx_items(int uart_idx = 0);
    uart_item item;
    forever begin
      p_sequencer.uart_tx_fifos[uart_idx].get(item);
      `uvm_info(`gfn, $sformatf("Received UART data over TX:\n%0h", item.data), UVM_HIGH)
      uart_tx_data_q.push_back(item.data);
    end
  endtask

  // Shorten the alert handler ping timer wait cycles.
  //
  // This is done to speed up the simulation while achieving coverage on alert pings to various
  // blocks.
  // TODO; plusargs should be sought in a singla place (we do it in the base test class).
  // TODO: Nothing may happen after calling this function, becuase it internally fetches a plusarg
  // which can result in a nop. Refactor this later.
  task alert_ping_en_shorten();
    bit shorten_ping_en;
    void'($value$plusargs("shorten_ping_en=%0d", shorten_ping_en));
    if (shorten_ping_en) begin
      void'(cfg.chip_vif.signal_probe_alert_handler_ping_timer_wait_cyc_mask_i(
          SignalProbeForce, 16'h3F));
    end
  endtask : alert_ping_en_shorten

  // Initialize the OTP creator SW cfg region to use otbn for signature verification.
  virtual function void initialize_otp_sig_verify();
    // Use otbn mod_exp implementation for signature
    // verification. See the definition of `hardened_bool_t` in
    // sw/device/lib/base/hardened.h.
    cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgSigverifyRsaModExpIbexEnOffset,
                                     32'h1d4);
  endfunction : initialize_otp_sig_verify

  // Initialize the OTP creator SW cfg region with AST configuration data.
  virtual function void initialize_otp_creator_sw_cfg_ast_cfg();
    // The knob controls whether the AST is actually programmed.
    if (cfg.do_creator_sw_cfg_ast_cfg) begin
      cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstInitEnOffset,
                                       prim_mubi_pkg::MuBi4True);
    end

    // Ensure that the allocated size of the AST cfg region in OTP is equal to the number of AST
    // registers to be programmed.
    `DV_CHECK_EQ_FATAL(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgSize, ast_pkg::AstRegsNum * 4)
    foreach (cfg.creator_sw_cfg_ast_cfg_data[i]) begin
      `uvm_info(`gfn, $sformatf(
                "OTP: Preloading creator_sw_cfg_ast_cfg_data[%0d] with 0x%0h via backdoor",
                i,
                cfg.creator_sw_cfg_ast_cfg_data[i]
                ), UVM_MEDIUM)
      cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset + i * 4,
                                       cfg.creator_sw_cfg_ast_cfg_data[i]);
    end
  endfunction

  // Set the ROM_EXEC_EN bit in OTP if we are not in RAW state
  virtual function void set_otp_creator_sw_cfg_rom_exec_en(bit [31:0] value);
    lc_ctrl_state_pkg::lc_state_e lc_state;
    logic [31:0] otp_raw_val;
    logic [31:0] chk_vector;

    // Set rom_exec_en only when we are not in RAW state.
    lc_state = cfg.mem_bkdr_util_h[Otp].otp_read_lc_partition_state();

    // If we are already 1, we cannot set to 0.
    // This should probably be relocated to mem_bkdr_util eventually as an option for writes
    otp_raw_val = cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorSwCfgRomExecEnOffset);
    chk_vector = ~value & (otp_raw_val ^ value);
    `DV_CHECK(chk_vector == '0);

    if (lc_state != LcStRaw) begin
      `uvm_info(`gfn, "Automatically set rom_exec_en", UVM_LOW)
      cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgRomExecEnOffset, value);
    end
  endfunction

  task test_mem_rw(uvm_mem mem, int max_access = 2048);
    int unsigned expected_data[int unsigned];
    int offmax = mem.get_size() - 1;
    int sizemax = offmax / 4;

    `uvm_info(`gfn, $sformatf("Mem writes to %s %0d times", mem.get_full_name(), max_access),
              UVM_MEDIUM)

    for (int i = 0; i < max_access; ++i) begin
      int unsigned offset = $urandom_range(sizemax, 0);

      int unsigned wdata = $urandom();
      expected_data[offset] = wdata;
      `uvm_info(`gfn, $sformatf("Writing 0x%x to offset 0x%x in %s", wdata, offset, mem.get_name()),
                UVM_MEDIUM)

      if (mem.get_access() == "RW") begin
        mem_wr(.ptr(mem), .offset(offset), .data(wdata));
      end else begin  // if (mem.get_access() == "RW")
        // deposit random data to rom
        int byte_addr = offset * 4;
        cfg.mem_bkdr_util_h[Rom].rom_encrypt_write32_integ(
            .addr(byte_addr), .data(wdata), .key(RndCnstRomCtrlScrKey),
            .nonce(RndCnstRomCtrlScrNonce), .scramble_data(1));
      end
    end

    `uvm_info(`gfn, $sformatf("Writes to %s is complete, read back start...", mem.get_full_name()),
              UVM_MEDIUM)

    foreach (expected_data[address]) begin
      int unsigned rdata;
      int unsigned exp_data = expected_data[address];

      mem_rd(.ptr(mem), .offset(address), .data(rdata));
      `DV_CHECK_EQ(rdata, exp_data, $sformatf(
                   "read back check for offset 0x%x failed, got 0x%x, expected 0x%x",
                    address, rdata, exp_data))
    end
    `uvm_info(`gfn, $sformatf("read check from %s is complete", mem.get_full_name()),
              UVM_MEDIUM)

  endtask : test_mem_rw

  // POR_N needs to stay asserted for at least 6 AON clock cycles.
  task assert_por_reset(int delay = 0);
    repeat (delay) @cfg.chip_vif.pwrmgr_low_power_if.fast_cb;
    cfg.chip_vif.por_n_if.drive(0);
    repeat (6) @cfg.chip_vif.pwrmgr_low_power_if.cb;
    cfg.clk_rst_vif.wait_clks(10);
    cfg.chip_vif.por_n_if.drive(1);
  endtask // assert_por_reset

endclass : chip_base_vseq
