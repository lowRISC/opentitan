// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_env_cfg extends cip_base_env_cfg#(
    .RAL_T(chip_reg_block)
);

  // Testbench settings
  bit stub_cpu;
  bit en_uart_logger;
  int uart_baud_rate = uart_agent_pkg::BaudRate2Mbps;
  bit use_gpio_for_sw_test_status;
  bit initialize_ram;

  // Write logs from sw test to separate log file as well, in addition to the simulator log file.
  bit write_sw_logs_to_file = 1'b1;

  // chip top interfaces
  virtual clk_rst_if usb_clk_rst_vif;
  gpio_vif gpio_vif;
  mem_bkdr_vif mem_bkdr_vifs[chip_mem_e];
  virtual pins_if #(1) srst_n_vif;
  virtual pins_if #(1) jtag_spi_n_vif;
  virtual pins_if #(1) bootstrap_vif;
  virtual pins_if #(1) rst_n_mon_vif;

  // sw logger related
  string sw_types[] = '{"rom", "sw"};
  sw_logger_vif sw_logger_vif;
  int sw_image_widths[] = '{32, 64};
  string sw_images[string];
  virtual sw_test_status_if sw_test_status_vif;
  uint sw_test_timeout_ns = 5_000_000;  // 5ms

  // ext component cfgs
  rand uart_agent_cfg m_uart_agent_cfg;
  rand jtag_agent_cfg m_jtag_agent_cfg;
  rand spi_agent_cfg m_spi_agent_cfg;

  `uvm_object_utils_begin(chip_env_cfg)
    `uvm_field_int(stub_cpu, UVM_DEFAULT)
    `uvm_field_object(m_uart_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_jtag_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_spi_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  // TODO: Fixing core clk freq to 50MHz for now.
  // Need to find a way to pass this to the SW test.
  constraint clk_freq_mhz_c {clk_freq_mhz == dv_utils_pkg::ClkFreq50Mhz;}

  `uvm_object_new

  virtual function void initialize_csr_addr_map_size();
    this.csr_addr_map_size = 1 << TL_AW;
  endfunction : initialize_csr_addr_map_size

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    chip_mem_e mems[] = {Rom, Ram, FlashBank0, FlashBank1};

    has_devmode = 0;

    super.initialize(csr_base_addr);
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

    // initialize the sw_image names and log file names
    foreach (sw_types[i]) begin
      sw_images[sw_types[i]] = $sformatf("%0s.%0d.vmem", sw_types[i], sw_image_widths[i]);
    end
  endfunction

  // ral flow is limited in terms of setting correct field access policies and reset values
  // We apply those fixes here - please note these fixes need to be reflected in the scoreboard
  protected virtual function void apply_ral_fixes();
    // Out of reset, the link is in disconnected state.
    ral.usbdev.intr_state.disconnected.set_reset(1'b1);

    // ram_main mem and hmac mem support partial write
    ral.ram_main.set_mem_partial_write_support(1);
    ral.ram_ret.set_mem_partial_write_support(1);
    ral.hmac.msg_fifo.set_mem_partial_write_support(1);
  endfunction

endclass
