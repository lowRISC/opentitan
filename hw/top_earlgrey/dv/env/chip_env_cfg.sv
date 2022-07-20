// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_env_cfg #(type RAL_T = chip_ral_pkg::chip_reg_block) extends cip_base_env_cfg #(
    .RAL_T(RAL_T)
  );

  // Testbench settings
  bit                 stub_cpu;
  bit                 en_uart_logger;
  uart_agent_pkg::baud_rate_e uart_baud_rate = uart_agent_pkg::BaudRate1Mbps;
  bit                 use_gpio_for_sw_test_status;

  // Write logs from sw test to separate log file as well, in addition to the simulator log file.
  bit                 write_sw_logs_to_file = 1'b1;

  // use spi or backdoor to load bootstrap
  bit                 use_spi_load_bootstrap = 0;

  // chip top interfaces
  gpio_vif            gpio_vif;
  virtual pins_if#(2) tap_straps_vif;
  virtual pins_if#(2) dft_straps_vif;
  virtual pins_if#(3) sw_straps_vif;
  virtual pins_if#(1) rst_n_mon_vif;
  virtual clk_rst_if  cpu_clk_rst_vif;
  virtual pins_if#(1) pinmux_wkup_vif;
  virtual pins_if#(1) por_rstn_vif;
  virtual pins_if#(1) pwrb_in_vif;
  virtual pins_if#(1) ec_rst_vif;
  virtual pins_if#(1) flash_wp_vif;
  virtual pins_if#(8) sysrst_ctrl_vif;

  // pwrmgr probe interface
  virtual pwrmgr_low_power_if   pwrmgr_low_power_vif;

  // Memory backdoor util instances for all memory instances in the chip.
  mem_bkdr_util mem_bkdr_util_h[chip_mem_e];

  // Creator SW config region in OTP that holds the AST config data. Randomized for open source.
  //
  // These are written via backdoor to the OTP region that starts at
  // otp_ctrl_reg_pkg::CreatorSwCfgAstCfgOffset. SW based tests (via test ROM or the production mask
  // ROM) will read out from this OTP region and write blindly to AST at the start. Non-SW based
  // tests will do the same, prior to the test starting, see
  // chip_stub_cpu_base_vseq::dut_init().
  //
  // In closed source, tests can modify this data directly in the extended sequence's dut_init(),
  // before invoking super.dut_init(), or any other suitable place.
  rand uint creator_sw_cfg_ast_cfg_data[ast_pkg::AstRegsNum];

  // A knob that controls whether the AST initialization is done, enabled by default.
  // Can be updated with plusarg.
  bit do_creator_sw_cfg_ast_cfg = 1;

  // sw related
  // In OpenTitan, the same SW test image can be built for DV, Verilator and FPGA. SW build for
  // other platforms can be run on DV as well. We allow that by specifying the SW build device.
  string sw_build_device = "sim_dv";

  // Types of SW images used in the test.
  //
  // Set via plusarg. This is the basename of the SW image. If the SW image is not pre-built
  // (e.g., generated with Bazel), then the ~sw_build_device~ is suffixed to the basename to
  // pick the correct image. The following files (extensions) with this basename are expected
  // to exist there:
  // - .elf:          embedded executable
  // - .32.vmem:      mem image with 32-bit word size (for boot ROM)
  // - .64.vmem:      mem image with 64-bit word size (for sw_test / flash load)
  // - .frames.vmem:  mem image converted with spiflash frames (for tests with boostrap enabled)
  // - .rodata.txt:   dump of RO sections of the SW
  // - .logs.txt:     dump of SW logs
  //
  // The ~resolve_sw_image_paths()~ function does the job of suffixing this path with
  // ~sw_build_device~.
  string sw_images[sw_type_e];
  string sw_image_flags[sw_type_e][$];

  // Maintain a list of generated OTP images.
  lc_ctrl_state_pkg::lc_state_e use_otp_image = lc_ctrl_state_pkg::LcStRma;
  string otp_images[lc_ctrl_state_pkg::lc_state_e];

  uint               sw_test_timeout_ns = 12_000_000; // 12ms
  sw_logger_vif      sw_logger_vif;
  sw_test_status_vif sw_test_status_vif;
  ast_supply_vif     ast_supply_vif;
  ast_ext_clk_vif    ast_ext_clk_vif;

  // Number of RAM tiles for each RAM instance.
  uint num_ram_main_tiles;
  uint num_ram_ret_tiles;

  // ext component cfgs
  rand uart_agent_cfg       m_uart_agent_cfgs[NUM_UARTS];
  rand jtag_riscv_agent_cfg m_jtag_riscv_agent_cfg;
  rand jtag_agent_cfg       m_jtag_agent_cfg;
  rand spi_agent_cfg        m_spi_agent_cfg;
  pwm_monitor_cfg           m_pwm_monitor_cfg[NUM_PWM_CHANNELS];

  // JTAG DMI register model
  rand jtag_dmi_reg_block jtag_dmi_ral;
  // A constant that can be referenced from anywhere.
  string rv_dm_rom_ral_name = "rv_dm_debug_mem_reg_block";
  parameter uint RV_DM_JTAG_IDCODE = `BUILD_SEED;
  // Design uses 5 bits for IR.
  parameter uint JTAG_IR_LEN = 5;

  `uvm_object_utils_begin(chip_env_cfg)
    `uvm_field_int   (stub_cpu,               UVM_DEFAULT)
    `uvm_field_object(m_jtag_riscv_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_spi_agent_cfg,        UVM_DEFAULT)
    `uvm_field_object(jtag_dmi_ral,           UVM_DEFAULT)
  `uvm_object_utils_end

  constraint clk_freq_mhz_c {
    clk_freq_mhz inside {48, 96};
    foreach (clk_freqs_mhz[i]) clk_freqs_mhz[i] == clk_freq_mhz;
  }

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    ext_clk_type_e ext_clk_type = UseInternalClk;
    has_devmode = 0;
    list_of_alerts = chip_env_pkg::LIST_OF_ALERTS;

    // Set up second RAL model for ROM memory and associated collateral
    if (use_jtag_dmi == 1) begin
      ral_model_names.push_back(rv_dm_rom_ral_name);
      clk_freqs_mhz[rv_dm_rom_ral_name] = clk_freq_mhz;
    end

    super.initialize(csr_base_addr);
    `uvm_info(`gfn, $sformatf("ral_model_names: %0p", ral_model_names), UVM_LOW)

    // Set the a_source width limitation for the TL agent hooked up to the CPU cored port.
    // TODO: use a parameter (or some better way)?
    m_tl_agent_cfg.valid_a_source_width = 6;

    // create uart agent config obj
    foreach (m_uart_agent_cfgs[i]) begin
      m_uart_agent_cfgs[i] = uart_agent_cfg::type_id::create($sformatf("m_uart_agent_cfg%0d", i));
    end

    // create jtag agent config obj
    m_jtag_riscv_agent_cfg = jtag_riscv_agent_cfg::type_id::create("m_jtag_riscv_agent_cfg");
    m_jtag_riscv_agent_cfg.use_jtag_dmi = use_jtag_dmi;
    if (use_jtag_dmi == 1) begin
      // Both, the regs and the debug mem TL device (in the DUT) only support 1 outstanding.
      m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 1;
      m_tl_agent_cfgs[rv_dm_rom_ral_name].max_outstanding_req = 1;

      m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");
      m_jtag_agent_cfg.if_mode = dv_utils_pkg::Host;
      m_jtag_agent_cfg.is_active = 1'b1;
      m_jtag_agent_cfg.ir_len = JTAG_IR_LEN;

      // Set the 'correct' IDCODE register value to the JTAG DTM RAL.
      m_jtag_agent_cfg.jtag_dtm_ral.idcode.set_reset(RV_DM_JTAG_IDCODE);
      m_jtag_riscv_agent_cfg.m_jtag_agent_cfg = m_jtag_agent_cfg;
    end

    // create spi agent config obj
    m_spi_agent_cfg = spi_agent_cfg::type_id::create("m_spi_agent_cfg");

    // create pwm monitor config obj
    foreach (m_pwm_monitor_cfg[i]) begin
      m_pwm_monitor_cfg[i] = pwm_monitor_cfg::type_id::create($sformatf("m_pwm_monitor%0d_cfg", i));
      m_pwm_monitor_cfg[i].is_active = 0;
    end

    // By default, assume these OTP image paths.
    otp_images[lc_ctrl_state_pkg::LcStRaw] = "otp_ctrl_img_raw.vmem";
    otp_images[lc_ctrl_state_pkg::LcStDev] = "otp_ctrl_img_dev.vmem";
    otp_images[lc_ctrl_state_pkg::LcStRma] = "otp_ctrl_img_rma.vmem";

    `DV_CHECK_LE_FATAL(num_ram_main_tiles, 16)
    `DV_CHECK_LE_FATAL(num_ram_ret_tiles, 16)

    // Set external clock frequency.
    `DV_GET_ENUM_PLUSARG(ext_clk_type_e, ext_clk_type, ext_clk_type)
    case (ext_clk_type)
      UseInternalClk: ; // clk_freq_mhz can be a random value
      ExtClkLowSpeed:  clk_freq_mhz = 48;
      ExtClkHighSpeed: clk_freq_mhz = 96;
      default: `uvm_fatal(`gfn, $sformatf("Unexpected ext_clk_type: %s", ext_clk_type.name))
    endcase // case (ext_clk_type)

    // ral_model_names = chip_reg_block // 1 entry
    if (use_jtag_dmi == 1) begin
      clk_freqs_mhz[rv_dm_rom_ral_name] = clk_freq_mhz;
      jtag_dmi_ral = create_jtag_dmi_reg_block(m_jtag_riscv_agent_cfg.m_jtag_agent_cfg);
      // Fix the reset values of these fields based on our design.
      `uvm_info(`gfn, "Fixing reset values in jtag_dmi_ral", UVM_LOW)
      jtag_dmi_ral.hartinfo.dataaddr.set_reset(dm::DataAddr);
      jtag_dmi_ral.hartinfo.datasize.set_reset(dm::DataCount);
      jtag_dmi_ral.hartinfo.dataaccess.set_reset(1);  // TODO: verify this!
      jtag_dmi_ral.hartinfo.nscratch.set_reset(2);  // TODO: verify this!
      jtag_dmi_ral.abstractcs.datacount.set_reset(dm::DataCount);
      jtag_dmi_ral.abstractcs.progbufsize.set_reset(dm::ProgBufSize);
      jtag_dmi_ral.dmstatus.authenticated.set_reset(1);  // No authentication performed.
      jtag_dmi_ral.sbcs.sbaccess32.set_reset(1);
      jtag_dmi_ral.sbcs.sbaccess16.set_reset(1);
      jtag_dmi_ral.sbcs.sbaccess8.set_reset(1);
      jtag_dmi_ral.sbcs.sbasize.set_reset(32);
      apply_jtag_dmi_ral_csr_excl();
    end
  endfunction

  // Apply RAL fixes before it is locked.
  protected virtual function void post_build_ral_settings(dv_base_reg_block ral);
    RAL_T chip_ral;
    super.post_build_ral_settings(ral);
    if (!$cast(chip_ral, ral)) return;
    // Out of reset, the link is in disconnected state.
    chip_ral.usbdev.intr_state.disconnected.set_reset(1'b1);
    if (ral.get_name() == rv_dm_rom_ral_name) begin
      rv_dm_debug_mem_reg_block debug_mem_ral;
      uvm_reg regs[$];

      ral.get_registers(regs);
      foreach (regs[i]) begin
        regs[i].clear_hdl_path("ALL");
      end

      // ROM within the debug mem is RO - it ignores writes instead of throwing an error response.
      `downcast(debug_mem_ral, ral)
      debug_mem_ral.rom.set_write_to_ro_mem_ok(1);
      debug_mem_ral.rom.set_mem_partial_write_support(1);

      // TODO(#10837): Accesses to unmapped regions of debug mem RAL space does not return an error
      // response. Fix this if design is updated.
      debug_mem_ral.set_unmapped_access_ok(1);

      // Debug mem does not error on any type of sub-word writes.
      debug_mem_ral.set_supports_sub_word_csr_writes(1);
    end
  endfunction

  // Apply RAL exclusions externally since the RAL itself is considered generic. The IP it is used
  // in constrains the RAL with its implementation details.
  virtual function void apply_jtag_dmi_ral_csr_excl();
    csr_excl_item csr_excl = jtag_dmi_ral.get_excl_item();

    // We leave the DM 'activated' for CSR tests to reduce noise. We exclude this from further
    // writes to avoid side-effects.
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.dmactive.get_full_name(),
        CsrExclWrite, CsrNonInitTests);

    // This field is tied off to 0 due to no hart array mask being implemented.
    // TODO: Change these to access policy.
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hasel.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hartreset.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // Selecting a different hart in the middle of random read/writes impact other registers.
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hartsello.get_full_name(),
        CsrExclWrite, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hartselhi.get_full_name(),
        CsrExclWrite, CsrNonInitTests);

    // Writes to other CSRs may affect dmstatus, even the HW reset test.
    csr_excl.add_excl(jtag_dmi_ral.dmstatus.get_full_name(), CsrExclCheck, CsrAllTests);

    // We have only upto dm::DataCount number of these registers available.
    foreach (jtag_dmi_ral.abstractdata[i]) begin
      if (i >= dm::DataCount) begin
        csr_excl.add_excl(jtag_dmi_ral.abstractdata[i].get_full_name(),
            CsrExclWriteCheck, CsrNonInitTests);
      end
    end

    // We have only upto dm::ProgBufSize number of these registers available.
    foreach (jtag_dmi_ral.progbuf[i]) begin
      if (i >= dm::ProgBufSize) begin
        csr_excl.add_excl(jtag_dmi_ral.progbuf[i].get_full_name(),
            CsrExclWriteCheck, CsrNonInitTests);
      end
    end

    // These prevent an SBA access from being triggered, which have other side effects.
    csr_excl.add_excl(jtag_dmi_ral.sbcs.sbreadondata.get_full_name(),
        CsrExclWrite, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbcs.sbreadonaddr.get_full_name(),
        CsrExclWrite, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbdata0.get_full_name(),
        CsrExclWrite, CsrNonInitTests);

    // TODO: This should be an access policy change.
    csr_excl.add_excl(jtag_dmi_ral.sbcs.sbaccess.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // These SBA registers are not implemented, or unsupported due to 32-bit system.
    csr_excl.add_excl(jtag_dmi_ral.sbaddress1.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbaddress2.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbaddress3.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbdata2.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbdata3.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // Abstractcs cmderr bits are updated by RTL.
    csr_excl.add_excl(jtag_dmi_ral.abstractcs.cmderr.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // Not all bits of abstractauto are set - and its also impacted by writes to other CSRs.
    csr_excl.add_excl(jtag_dmi_ral.abstractauto.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
  endfunction


  // Parse a space-separated list of sw_images supplied as a string.
  //
  // The typical usecase is the list of SW images used by the test supplied as a plusarg. The
  // SW images are defined by their filename. Each SW image can have additional metadata
  // specified using ":" as delimiters. Examples:
  // +sw_images="test_binary_1:1 test_binary_2:0"
  // +sw_images="foo:0:flag1 bar:1:flag1:flag2".
  //
  // The index (optional) is mapped to the type of SW image (enumerated in sw_type_e). If index is
  // not specified, then `SwTypeTest` is assumed. Flags (optional) are arbitrary strings attached to
  // the SW image. They can be used to treat the SW image in a specific way. The flag "signed" for
  // example, is used to set the SW image extension correctly.
  virtual function void parse_sw_images_string(string sw_images_string);
    string sw_images_split[$];

    // Split sw_images with space.
    str_utils_pkg::str_split(sw_images_string, sw_images_split, ",");
    `DV_CHECK_GT_FATAL(sw_images_split.size(), 0)

    foreach (sw_images_split[i]) begin
      sw_type_e sw_type;
      string sw_image_fields[$];

      // Split each entry with ':' into sw_image_fields.
      str_utils_pkg::str_split(sw_images_split[i], sw_image_fields, ":");
      `DV_CHECK_GT_FATAL(sw_image_fields.size(), 0)

      if (sw_image_fields.size() == 1) begin
        sw_images[SwTypeTest] = sw_image_fields[0];
        continue;
      end

      // There are at least 2 fields - first is the filename, second is the index (SW type).
      sw_type = sw_type_e'(sw_image_fields[1].atoi());
      sw_images[sw_type] = sw_image_fields[0];
      if (sw_image_fields.size() > 2) begin
        sw_image_flags[sw_type] = sw_image_fields[2:$];
      end
    end
    resolve_sw_image_paths();
  endfunction

  // Finalize the SW image paths, once all SW image settings are done.
  virtual function void resolve_sw_image_paths();
    foreach (sw_images[i]) begin
      if ("prebuilt" inside {sw_image_flags[i]}) begin
        sw_images[i] = $sformatf("%0s", sw_images[i]);
      end else if ("signed" inside {sw_image_flags[i]}) begin
        // TODO: support multiple signing keys. See "signing_keys" in
        // `rules/opentitan.bzl` for options.
        sw_images[i] = $sformatf("%0s_prog_%0s.test_key_0.signed", sw_images[i], sw_build_device);
      end else begin
        if (i == SwTypeTest) begin
          sw_images[i] = $sformatf("%0s_prog_%0s", sw_images[i],
            sw_build_device);
        end else begin
          sw_images[i] = $sformatf("%0s_%0s", sw_images[i], sw_build_device);
        end
      end
    end
  endfunction

endclass
