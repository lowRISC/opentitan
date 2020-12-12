// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_env_cfg extends cip_base_env_cfg #(.RAL_T(chip_reg_block));

  // Testbench settings
  bit                 stub_cpu;
  bit                 en_uart_logger;
  int                 uart_baud_rate = uart_agent_pkg::BaudRate1Mbps;
  bit                 use_gpio_for_sw_test_status;
  bit                 initialize_ram;

  // Write logs from sw test to separate log file as well, in addition to the simulator log file.
  bit                 write_sw_logs_to_file = 1'b1;

  // use spi or backdoor to load bootstrap
  bit                 use_spi_load_bootstrap = 0;

  // chip top interfaces
  virtual clk_rst_if  usb_clk_rst_vif;
  gpio_vif            gpio_vif;
  mem_bkdr_vif        mem_bkdr_vifs[chip_mem_e];
  virtual pins_if#(1) srst_n_vif;
  virtual pins_if#(1) jtag_spi_n_vif;
  virtual pins_if#(1) bootstrap_vif;
  virtual pins_if#(1) rst_n_mon_vif;

  // sw related
  // Directory from where to pick up the SW test images -default to PWD {run_dir}.
  string              sw_build_bin_dir = ".";

  // In OpenTitan, the same SW test image can be built for DV, Verilator and FPGA. SW build for
  // other platforms can be run on DV as well. We allow that by specifying the SW build device.
  string              sw_build_device = "sim_dv";

  // Types of SW images used in the test.
  //
  // Set via plusarg. This is the path (relative to ~sw_build_bin_dir~) upto the basename of the SW
  // image. If the SW image is not pre-built (generated with meson), then the ~sw_build_device~ is
  // suffixed to the basename to pick the correct image. The following files (extensions) with this
  // basename are expected to exist there:
  // - .elf:          embedded executable
  // - .32.vmem:      mem image with 32-bit word size (for boot_rom)
  // - .64.vmem:      mem image with 64-bit word size (for sw_test / flash load)
  // - .frames.vmem:  mem image converted with spiflash frames (for tests with boostrap enabled)
  // - .rodata.txt:   dump of RO sections of the SW
  // - .logs.txt:     dump of SW logs
  //
  // The ~resolve_sw_image_paths()~ function does the job of prefixing this path with
  // ~sw_build_bin_dir and suffixing with ~sw_build_device~.
  string              sw_images[sw_type_e];
  string              sw_image_flags[sw_type_e][$];

  uint                sw_test_timeout_ns = 5_000_000; // 5ms
  sw_logger_vif       sw_logger_vif;
  sw_test_status_vif  sw_test_status_vif;

  // ext component cfgs
  rand uart_agent_cfg m_uart_agent_cfg;
  rand jtag_agent_cfg m_jtag_agent_cfg;
  rand spi_agent_cfg  m_spi_agent_cfg;

  `uvm_object_utils_begin(chip_env_cfg)
    `uvm_field_int   (stub_cpu,             UVM_DEFAULT)
    `uvm_field_object(m_uart_agent_cfg,     UVM_DEFAULT)
    `uvm_field_object(m_jtag_agent_cfg,     UVM_DEFAULT)
    `uvm_field_object(m_spi_agent_cfg,      UVM_DEFAULT)
  `uvm_object_utils_end

  // TODO: Fixing core clk freq to 50MHz for now.
  // Need to find a way to pass this to the SW test.
  constraint clk_freq_mhz_c {
    clk_freq_mhz == dv_utils_pkg::ClkFreq50Mhz;
  }

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    chip_mem_e mems[] = {Rom,
                         RamMain,
                         RamRet,
                         FlashBank0,
                         FlashBank1,
                         FlashBank0Info,
                         FlashBank1Info,
                         Otp};

    has_devmode = 0;
    list_of_alerts = chip_env_pkg::LIST_OF_ALERTS;

    super.initialize(csr_base_addr);

    // Set the a_source width limitation for the TL agent hooked up to the CPU cored port.
    // TODO: use a parameter (or some better way)?
    m_tl_agent_cfg.valid_a_source_width = 6;

    // create uart agent config obj
    m_uart_agent_cfg = uart_agent_cfg::type_id::create("m_uart_agent_cfg");

    // create jtag agent config obj
    m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");

    // create spi agent config obj
    m_spi_agent_cfg = spi_agent_cfg::type_id::create("m_spi_agent_cfg");

    // initialize the mem_bkdr_if vifs we want for this chip
    foreach (mems[mem]) begin
      mem_bkdr_vifs[mems[mem]] = null;
    end

    // By default, assume SW images in PWD with these generic names.
    sw_images[SwTypeRom] = "./rom";
    sw_images[SwTypeTest] = "./sw";
    sw_images[SwTypeOtbn] = "./otbn";
  endfunction

  // ral flow is limited in terms of setting correct field access policies and reset values
  // We apply those fixes here - please note these fixes need to be reflected in the scoreboard
  protected virtual function void apply_ral_fixes();
    // Out of reset, the link is in disconnected state.
    ral.usbdev.intr_state.disconnected.set_reset(1'b1);
  endfunction

  // Parse a space-separated list of sw_images supplied as a string.
  //
  // The typical usecase is the list of SW images used by the test supplied as a plusarg. Each
  // SW image can have additional metadata specified using ":" as delimiters. Examples:
  // +sw_images="path/to/sw/test1:1 path/to/sw/test2:0"
  // +sw_images="foo/bar:0:flag1 bar/baz:1:flag1:flag2 quux/foo:2:flag3".
  //
  // The index (optional) is mapped to the type of SW image (enumerated in sw_type_e). If index is
  // not specified, then `SwTypeTest` is assumed. Flags (optional) are arbitrary strings attached to
  // the SW image. They can be used to treat the SW image in a specific way. The flag "prebuilt" for
  // example, is used to set the SW image path correctly.
  virtual function void parse_sw_images_string(string sw_images_string);
    string sw_images_split[$];

    // Split sw_images with space.
    str_utils_pkg::str_split(sw_images_string, sw_images_split);
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

      // There are at least 2 fields - first is the path, second is the index (SW type).
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
        sw_images[i] = $sformatf("%0s/%0s", sw_build_bin_dir, sw_images[i]);
      end else begin
        sw_images[i] = $sformatf("%0s/%0s_%0s", sw_build_bin_dir, sw_images[i], sw_build_device);
      end
    end
  endfunction

endclass
