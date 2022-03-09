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

  typedef enum int {ExtClkFreq48MHz = 48, ExtClkFreq100MHz = 100} ext_clk_freq_e;

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

  virtual task dut_init(string reset_kind = "HARD");
    // Initialize gpio pin default states
    cfg.gpio_vif.set_pulldown_en({chip_env_pkg::NUM_GPIOS{1'b1}});
    // Initialize flash seeds
    cfg.mem_bkdr_util_h[FlashBank0Info].set_mem();
    cfg.mem_bkdr_util_h[FlashBank1Info].set_mem();
    // Backdoor load the OTP image.
    cfg.mem_bkdr_util_h[Otp].load_mem_from_file(cfg.otp_images[cfg.use_otp_image]);
    initialize_otp_creator_sw_cfg_ast_cfg();
    // Randomize the ROM image. Subclasses that have an actual ROM image will load it later.
    cfg.mem_bkdr_util_h[Rom].randomize_mem();
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
  endtask

  virtual task dut_shutdown();
    // check for pending chip operations and wait for them to complete
    // TODO
  endtask

  virtual task pre_start();
    // Do DUT init after some additional settings.
    bit do_dut_init_save = do_dut_init;
    int extclk_frequency_mhz = ExtClkFreq100MHz;
    int extclk_frequency_attempted;
    do_dut_init = 1'b0;
    super.pre_start();
    do_dut_init = do_dut_init_save;

    // Drive strap signals at the start.
    if (do_strap_pins_init) begin
      cfg.tap_straps_vif.drive(select_jtag);
      cfg.dft_straps_vif.drive(2'b00);
      cfg.sw_straps_vif.drive({2'b00, cfg.use_spi_load_bootstrap});
    end

    // Set external clock frequency.
    if ($value$plusargs("extclk_freq_mhz=%d", extclk_frequency_attempted)) begin
      if (extclk_frequency_attempted == ExtClkFreq100MHz ||
          extclk_frequency_attempted == ExtClkFreq48MHz) begin
        extclk_frequency_mhz = extclk_frequency_attempted;
      end else begin
        `uvm_error(`gfn, $sformatf(
                   "Unexpected extclk frequency %0d: valid numbers are 100 and 48",
                   extclk_frequency_attempted))
      end
    end
    cfg.clk_rst_vif.set_freq_mhz(extclk_frequency_mhz);

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

  // Initialize the OTP creator SW cfg region with AST configuration data.
  virtual function void initialize_otp_creator_sw_cfg_ast_cfg();
    // Ensure that the allocated size of the AST cfg region in OTP is greater than the number of AST
    // registers to be programmed.
    `DV_CHECK_GE_FATAL(otp_ctrl_reg_pkg::CreatorSwCfgAstCfgSize, ast_pkg::AstLastRegOffset)
    foreach (cfg.creator_sw_cfg_ast_cfg_data[i]) begin
      `uvm_info(`gfn, $sformatf({"OTP: Preloading creator_sw_cfg_ast_cfg_data[%0d] with 0x%0h ",
                                 "via backdoor"}, i, cfg.creator_sw_cfg_ast_cfg_data[i]),
                UVM_MEDIUM)
      cfg.mem_bkdr_util_h[Otp].write32(
          otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset + i * 4, cfg.creator_sw_cfg_ast_cfg_data[i]);
    end
    cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgAstInitEnOffset,
                                     prim_mubi_pkg::MuBi4True);
  endfunction

endclass : chip_base_vseq
