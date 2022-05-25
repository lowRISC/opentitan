// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_base_vseq #(type RAL_T = chip_ral_pkg::chip_reg_block) extends cip_base_vseq #(
    .CFG_T               (chip_env_cfg),
    .RAL_T               (RAL_T),
    .COV_T               (chip_env_cov),
    .VIRTUAL_SEQUENCER_T (chip_virtual_sequencer)
  );
  `uvm_object_utils(chip_base_vseq)

  // knobs to enable pre_start routines
  bit do_strap_pins_init = 1'b1; // initialize the strap

  // knobs to enable post_start routines

  // various knobs to enable certain routines

  // Local queue for holding received UART TX data.
  byte uart_tx_data_q[$];

  // Default value to drive JTAG tap during pre_start().
  chip_tap_type_e select_jtag = SelectRVJtagTap;

  `uvm_object_new

  virtual function void set_sva_check_rstreqs(bit enable);
    `uvm_info(`gfn, $sformatf("Remote setting check_rstreqs_en=%b", enable), UVM_MEDIUM)
    uvm_config_db#(bit)::set(null, "pwrmgr_rstmgr_sva_if", "check_rstreqs_en", enable);
  endfunction

  task post_start();
    do_clear_all_interrupts = 0;
    super.post_start();
    set_sva_check_rstreqs(0);
  endtask

  virtual task apply_reset(string kind = "HARD");
    // Note: The JTAG reset does not have a dedicated pad and is muxed with other chip IOs.
    // These IOs have pad attributes that are driven from registers, and as long as
    // the reset line of those registers is X, the registers and hence the pad outputs
    // will also be X. This causes the JTAG reset to not properly propagate, and hence we
    // have to assert the main reset before that (release can happen in a randomized way
    // via the apply_reset task later on).
    cfg.clk_rst_vif.drive_rst_pin(1'b0);
    // TODO: Cannot assert different types of resets in parallel; due to randomization
    // resets de-assert at different times. If the main rst_n de-asserts before others,
    // the CPU starts executing right away which can cause breakages.
    cfg.m_jtag_riscv_agent_cfg.m_jtag_agent_cfg.vif.do_trst_n();
    super.apply_reset(kind);
  endtask

  chip_callback_vseq callback_vseq;

  virtual task dut_init(string reset_kind = "HARD");
    // Initialize gpio pin default states
    if (!$test$plusargs("disable_gpio_pulldown")) begin
      cfg.gpio_vif.set_pulldown_en({chip_env_pkg::NUM_GPIOS{1'b1}});
    end
    // Initialize flash seeds
    cfg.mem_bkdr_util_h[FlashBank0Info].set_mem();
    cfg.mem_bkdr_util_h[FlashBank1Info].set_mem();
    // Backdoor load the OTP image.
    cfg.mem_bkdr_util_h[Otp].load_mem_from_file(cfg.otp_images[cfg.use_otp_image]);
    initialize_otp_sig_verify();
    initialize_otp_creator_sw_cfg_ast_cfg();
    callback_vseq.pre_dut_init();
    // Randomize the ROM image. Subclasses that have an actual ROM image will load it later.
    cfg.mem_bkdr_util_h[Rom].randomize_mem();
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
    callback_vseq.post_dut_init();
  endtask

  virtual task dut_shutdown();
    // check for pending chip operations and wait for them to complete
    // TODO
  endtask

  virtual task wait_rom_check_done();
    // The CSR tests (handled by this class) need to wait until the rom_ctrl block has finished
    // running KMAC before they can start issuing reads and writes. Otherwise, they might write to a
    // KMAC register while KMAC is in operation. This would have no effect and a subsequent read
    // from the register would show a mismatched value. We handle this by considering rom_ctrl's
    // operation as "part of reset".
    // Same for the test that uses jtag to access CSRs. We need to wait until rom check is done.
    //
    // Once the base class reset is finished, we're just after a chip reset. In a second, rom_ctrl
    // is going to start asking KMAC to do an operation. At that point, KMAC's CFG_REGWEN register
    // will go low. When the operation is finished, it will go high again. Wait until then.

    `uvm_info(`gfn, "waiting for rom_ctrl after reset", UVM_MEDIUM)
    // Use backdoor, so that this task can be used with or without stub mode enabled
    csr_spinwait(.ptr(ral.kmac.cfg_regwen), .exp_data(0), .backdoor(1), .spinwait_delay_ns(1000));
    `uvm_info(`gfn, "rom_ctrl check started", UVM_MEDIUM)
    csr_spinwait(.ptr(ral.kmac.cfg_regwen), .exp_data(1), .backdoor(1), .spinwait_delay_ns(1000));
    `uvm_info(`gfn, "rom_ctrl check done after reset", UVM_HIGH)
  endtask

  virtual task pre_start();
    // Do DUT init after some additional settings.
    bit do_dut_init_save = do_dut_init;
    do_dut_init = 1'b0;
    `uvm_create_on(callback_vseq, p_sequencer);
    `DV_CHECK_RANDOMIZE_FATAL(callback_vseq)
    super.pre_start();
    do_dut_init = do_dut_init_save;

    // Drive strap signals at the start.
    if (do_strap_pins_init) begin
      cfg.tap_straps_vif.drive(select_jtag);
      cfg.dft_straps_vif.drive(2'b00);
      cfg.sw_straps_vif.drive({2'b00, cfg.use_spi_load_bootstrap});
    end

    cfg.pinmux_wkup_vif.drive(1'b0);
    cfg.pwrb_in_vif.drive(1'b0);

    // Now safe to do DUT init.
    if (do_dut_init) dut_init();
  endtask

  // Grab packets sent by the DUT over the UART TX port.
  virtual task get_uart_tx_items(int uart_idx = 0);
    uart_item item;
    forever begin
      p_sequencer.uart_tx_fifos[uart_idx].get(item);
      `uvm_info(`gfn, $sformatf("Received UART data over TX:\n%0h", item.data), UVM_HIGH)
      uart_tx_data_q.push_back(item.data);
    end
  endtask

  // Initialize the OTP creator SW cfg region to use otbn for signature verification.
  virtual function void initialize_otp_sig_verify();
    // Use otbn mod_exp implementation for signature
    // verification. See the definition of `hardened_bool_t` in
    // sw/device/lib/base/hardened.h.
    cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgUseSwRsaVerifyOffset,
                                     32'h1d4);
  endfunction // initialize_otp_sig_verify

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
      `uvm_info(`gfn, $sformatf({"OTP: Preloading creator_sw_cfg_ast_cfg_data[%0d] with 0x%0h ",
                                 "via backdoor"}, i, cfg.creator_sw_cfg_ast_cfg_data[i]),
                UVM_MEDIUM)
      cfg.mem_bkdr_util_h[Otp].write32(
          otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset + i * 4, cfg.creator_sw_cfg_ast_cfg_data[i]);
    end
  endfunction

  task test_mem_rw(uvm_mem mem, int max_access = 2048);
    uvm_reg_data_t rdata;
    int wdata, exp_data[$]; // cause all data is 32bit wide in this test
    int offmax = mem.get_size() - 1;
    int sizemax = offmax / 4;
    int st, sz;
    int byte_addr;
    st = $urandom_range(0, offmax);
    // set the maximum transaction
    if (sizemax > max_access) sizemax = max_access;

    sz = $urandom_range(1, sizemax);
    `uvm_info(`gfn, $sformatf("Mem write to %s  offset:%0d size: %0d",
                              mem.get_full_name(), st, sz), UVM_MEDIUM)

    for (int i = 0; i < sz; ++i) begin
      wdata = $urandom();
      exp_data.push_back(wdata);

      if (mem.get_access() == "RW") begin
        mem_wr(.ptr(mem), .offset((st + i) % (offmax + 1)), .data(wdata));
      end else begin // if (mem.get_access() == "RW")
        // deposit random data to rom
        byte_addr = ((st + i) % (offmax + 1)) * 4;
        cfg.mem_bkdr_util_h[Rom].rom_encrypt_write32_integ(.addr(byte_addr), .data(wdata),
                                                           .key(RndCnstRomCtrlScrKey),
                                                           .nonce(RndCnstRomCtrlScrNonce),
                                                           .scramble_data(1));
      end
    end

    `uvm_info(`gfn, $sformatf("write to %s is complete, read back start...",
                                mem.get_full_name()), UVM_MEDIUM)
    for (int i = 0; i < sz; ++i) begin
      mem_rd(.ptr(mem), .offset((st + i) % (offmax + 1)), .data(rdata));
      `DV_CHECK_EQ((int'(rdata)), exp_data[i],
                   $sformatf("read back check for offset:%0d failed",
                             ((st + i) % (offmax + 1))))
    end
    `uvm_info(`gfn, $sformatf("read check from %s is complete",
                              mem.get_full_name()), UVM_MEDIUM)

  endtask : test_mem_rw

endclass : chip_base_vseq
