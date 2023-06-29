// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_base_test extends cip_base_test #(
    .ENV_T(chip_env),
    .CFG_T(chip_env_cfg)
  );
  `uvm_component_new
  `uvm_component_utils(chip_base_test)

  // The base class dv_base_test creates the following instances:
  // chip_env_cfg: cfg
  // chip_env:     env

  // The base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done.

  virtual function void build_phase(uvm_phase phase);
    string sw_images_plusarg;
    string use_otp_image_plusarg;

    super.build_phase(phase);

    // Knob to select the chip clock source.
    `DV_GET_ENUM_PLUSARG(chip_clock_source_e, cfg.chip_clock_source, chip_clock_source)
    if (cfg.chip_clock_source != ChipClockSourceInternal) begin
      cfg.clk_freq_mhz = cfg.chip_clock_source;
    end

    // Knob to set the UART baud rate (set to 2M by default).
    void'($value$plusargs("uart_baud_rate=%0d", cfg.uart_baud_rate));

    // The following plusargs are only valid for SW based tests (i.e., no stubbed CPU).
    // Knob to configure writing sw logs to a separate file (enabled by default).
    void'($value$plusargs("write_sw_logs_to_file=%0b", cfg.write_sw_logs_to_file));

    // Knob to enable logging over UART (disabled by default).
    void'($value$plusargs("en_uart_logger=%0b", cfg.en_uart_logger));
    cfg.m_uart_agent_cfgs[0].en_logger = cfg.en_uart_logger;
    cfg.m_uart_agent_cfgs[0].write_logs_to_file = cfg.write_sw_logs_to_file;

    // Knob to set the sw_test_timeout_ns (set to 12ms by default).
    void'($value$plusargs("sw_test_timeout_ns=%0d", cfg.sw_test_timeout_ns));

    // Knob to use SPI to load image via ROM bootstrap on first boot.
    // cfg.use_spi_load_bootstrap will be reset to 0 upon completion.
    void'($value$plusargs("use_spi_load_bootstrap=%0b", cfg.use_spi_load_bootstrap));

    // Knob to indicate what build device to use (DV, Verilator or FPGA).
    void'($value$plusargs("sw_build_device=%0s", cfg.sw_build_device));

    // Knob to set custom sw image names for rom and sw.
    if ($value$plusargs("sw_images=%0s", sw_images_plusarg)) begin
      cfg.parse_sw_images_string(sw_images_plusarg);
    end

    // Knob to perform the AST configuration.
    void'($value$plusargs("do_creator_sw_cfg_ast_cfg=%0b", cfg.do_creator_sw_cfg_ast_cfg));

    // Knob to use small page rma
    void'($value$plusargs("en_small_rma=%0b", cfg.en_small_rma));

    // Override the initial AST configuration data at runtime via plusarg.
    foreach (cfg.creator_sw_cfg_ast_cfg_data[i]) begin
      void'($value$plusargs({$sformatf("creator_sw_cfg_ast_cfg_data[%0d]", i), "=%0h"},
                            cfg.creator_sw_cfg_ast_cfg_data[i]));
    end

    // Knob to select the OTP image based on LC state.
    `DV_GET_ENUM_PLUSARG(otp_type_e, cfg.use_otp_image, use_otp_image)
    `DV_CHECK_FATAL(cfg.otp_images.exists(cfg.use_otp_image),
                    $sformatf({"Unsupported plusarg value: +use_otp_image=%0s. An image associated",
                               "with this LC state needs to be created first."}, cfg.use_otp_image))

    // Knob to skip ROM backdoor logging (for sims that use ROM macro).
    void'($value$plusargs("skip_rom_bkdr_load=%0b", cfg.skip_rom_bkdr_load));

    // Set the test timeout value to be sufficiently large.
    test_timeout_ns = 50_000_000;
    test_timeout_ns = `DV_MAX2(test_timeout_ns, 5 * cfg.sw_test_timeout_ns);
    `uvm_info(`gfn, $sformatf("test_timeout_ns = %0d", test_timeout_ns), UVM_LOW)
  endfunction : build_phase

endclass : chip_base_test
