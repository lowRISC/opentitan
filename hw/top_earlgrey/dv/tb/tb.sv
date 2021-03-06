// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import chip_env_pkg::*;
  import top_pkg::*;
  import chip_test_pkg::*;
  import xbar_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "chip_hier_macros.svh"

  wire clk, rst_n;
  wire usb_clk, usb_rst_n;

  wire [NUM_GPIOS-1:0] gpio_pins;

  wire jtag_tck;
  wire jtag_tms;
  wire jtag_trst_n;
  wire jtag_tdi;
  wire jtag_tdo;

  wire spi_device_sck;
  wire spi_device_csb;
  wire spi_device_sdo_o;
  wire spi_device_sdi_i;

  wire srst_n;
  wire jtag_spi_n;
  wire bootstrap;
  wire [7:0] io_dps;

  wire usb_dp0, usb_dn0, usb_sense0, usb_dppullup0, usb_dnpullup0;

  wire uart_rx, uart_tx;

  bit stub_cpu;
  bit en_sim_sram = 1'b1;

  // internal clocks and resets
  // cpu clock cannot reference cpu_hier since cpu clocks are forced off in stub_cpu mode
  wire cpu_clk = `CLKMGR_HIER.clocks_o.clk_proc_main;
  wire cpu_rst_n = `CPU_HIER.rst_ni;
  wire alert_handler_clk = `ALERT_HANDLER_HIER.clk_i;

  // interfaces
  clk_rst_if clk_rst_if(.clk, .rst_n);
  clk_rst_if usb_clk_rst_if(.clk(usb_clk), .rst_n(usb_rst_n));
  alert_esc_if alert_if[NUM_ALERTS](.clk(alert_handler_clk), .rst_n(rst_n));
  pins_if #(NUM_GPIOS) gpio_if(.pins(gpio_pins));
  pins_if #(1) srst_n_if(.pins(srst_n));
  pins_if #(1) jtag_spi_n_if(.pins(jtag_spi_n));
  pins_if #(1) bootstrap_if(.pins(bootstrap));
  pins_if #(1) rst_n_mon_if(.pins(cpu_rst_n));
  spi_if spi_if(.rst_n);
  tl_if cpu_d_tl_if(.clk(cpu_clk), .rst_n(cpu_rst_n));
  uart_if uart_if();
  jtag_if jtag_if();

  // TODO: Replace with correct interfaces once
  // pinmux/padring and pinout have been updated.
  wire [28:0] tie_off;
  wire [5:0] spi_host_tie_off;
  wire [1:0] spi_dev_tie_off;
  assign (weak0, weak1) tie_off = '0;
  assign (weak0, weak1) spi_host_tie_off = '0;
  assign (weak0, weak1) spi_dev_tie_off = '0;

  // backdoors
  bind `ROM_HIER mem_bkdr_if rom_mem_bkdr_if();
  bind `RAM_MAIN_HIER mem_bkdr_if #(.MEM_PARITY(1)) ram_mem_bkdr_if();
  bind `RAM_RET_HIER mem_bkdr_if #(.MEM_PARITY(1)) ram_mem_bkdr_if();
  bind `FLASH0_MEM_HIER mem_bkdr_if flash0_mem_bkdr_if();
  bind `FLASH1_MEM_HIER mem_bkdr_if flash1_mem_bkdr_if();
  bind `FLASH0_INFO_HIER mem_bkdr_if flash0_info_bkdr_if();
  bind `FLASH1_INFO_HIER mem_bkdr_if flash1_info_bkdr_if();
  bind `OTP_MEM_HIER mem_bkdr_if #(.MEM_ECC(1)) otp_bkdr_if();

  // TODO: the external clk is currently not connected.
  // We will need to feed this in via a muxed pin, once that function implemented.

  top_earlgrey_asic dut (
    // Clock and Reset
    .POR_N(rst_n),
    // Bank A (VIOA domain)
    .SPI_HOST_D0(spi_host_tie_off[0]),
    .SPI_HOST_D1(spi_host_tie_off[1]),
    .SPI_HOST_D2(spi_host_tie_off[2]),
    .SPI_HOST_D3(spi_host_tie_off[3]),
    .SPI_HOST_CLK(spi_host_tie_off[4]),
    .SPI_HOST_CS_L(spi_host_tie_off[5]),
    .SPI_DEV_D0(io_dps[1]),
    .SPI_DEV_D1(io_dps[2]),
    .SPI_DEV_D2(spi_dev_tie_off[0]),
    .SPI_DEV_D3(spi_dev_tie_off[1]),
    .SPI_DEV_CLK(io_dps[0]),
    .SPI_DEV_CS_L(io_dps[3]),
    .IOA0(gpio_pins[0]),   // MIO 0
    .IOA1(gpio_pins[1]),   // MIO 1
    .IOA2(gpio_pins[2]),   // MIO 2
    .IOA3(gpio_pins[3]),   // MIO 3
    .IOA4(gpio_pins[4]),   // MIO 4
    .IOA5(gpio_pins[5]),   // MIO 5
    // Bank B (VIOB domain)
    .IOB0(gpio_pins[6]),   // MIO 6
    .IOB1(gpio_pins[7]),   // MIO 7
    .IOB2(gpio_pins[8]),   // MIO 8
    .IOB3(gpio_pins[9]),   // MIO 9
    .IOB4(gpio_pins[10]),  // MIO 10
    .IOB5(gpio_pins[11]),  // MIO 11
    .IOB6(gpio_pins[12]),  // MIO 12
    .IOB7(gpio_pins[13]),  // MIO 13
    .IOB8(gpio_pins[14]),  // MIO 14
    .IOB9(gpio_pins[15]),  // MIO 15
    .IOB10(io_dps[6]),     // MIO 16
    .IOB11(io_dps[7]),     // MIO 17
    // Bank C (VCC domain)
    .IOC0(io_dps[4]),      // MIO 18
    .IOC1(io_dps[5]),      // MIO 19
    .IOC2(tie_off[0]),     // MIO 20
    .IOC3(tie_off[1]),     // MIO 21
    .IOC4(tie_off[2]),     // MIO 22
    .IOC5(jtag_spi_n),     // MIO 23 -- TAP_STRAP_SEL1
    .IOC6(tie_off[4]),     // MIO 24
    .IOC7(tie_off[5]),     // MIO 25
    .IOC8(tie_off[6]),     // MIO 26 -- TAP_STRAP_SEL0
    .IOC9(tie_off[7]),     // MIO 27
    .IOC10(tie_off[8]),    // MIO 28
    .IOC11(tie_off[9]),    // MIO 29
    // Bank R (VCC domain)
    .IOR0(tie_off[10]),    // MIO 30
    .IOR1(tie_off[11]),    // MIO 31
    .IOR2(uart_rx),        // MIO 32
    .IOR3(uart_tx),        // MIO 33
    .IOR4(tie_off[12]),    // MIO 34
    .IOR5(tie_off[13]),    // MIO 35
    .IOR6(tie_off[14]),    // MIO 36
    .IOR7(tie_off[15]),    // MIO 37
    .IOR8(tie_off[16]),    // MIO 38
    .IOR9(tie_off[17]),    // MIO 39
    .IOR10(tie_off[18]),   // MIO 40
    .IOR11(tie_off[19]),   // MIO 41
    .IOR12(tie_off[20]),   // MIO 42
    .IOR13(tie_off[21]),   // MIO 43
    // DCD (VCC domain)
    .CC1(tie_off[22]),
    .CC2(tie_off[23]),
    // USB (VCC domain)
    .USB_P(usb_dp0),
    .USB_N(usb_dn0),
    // FLASH
    .FLASH_TEST_MODE(tie_off[27:24]),
    .FLASH_TEST_VOLT(tie_off[28])
  );

  // connect signals
  assign io_dps[0]  = jtag_spi_n ? jtag_tck : spi_device_sck;
  assign io_dps[1]  = jtag_spi_n ? jtag_tdi : spi_device_sdi_i;
  assign io_dps[3]  = jtag_spi_n ? jtag_tms : spi_device_csb;
  assign (weak0, weak1) io_dps[4] = 1'b0;
  assign io_dps[5]  = srst_n;
  assign io_dps[6]  = jtag_spi_n;
  assign io_dps[7]  = bootstrap;
  assign spi_device_sdo_o  = jtag_spi_n ? 1'b0 : io_dps[2];
  assign jtag_tdo          = jtag_spi_n ? io_dps[2] : 1'b0;

  assign jtag_tck         = jtag_if.tck;
  assign jtag_tms         = jtag_if.tms;
  assign jtag_trst_n      = jtag_if.trst_n;
  assign jtag_tdi         = jtag_if.tdi;
  assign jtag_if.tdo      = jtag_tdo;

  assign spi_device_sck     = spi_if.sck;
  assign spi_device_csb     = spi_if.csb;
  assign spi_device_sdi_i   = spi_if.sio[0];
  assign spi_if.sio[1]      = spi_device_sdo_o;

  // TODO: Replace this weak pull to a known value with initialization
  // in the agent/interface.
  assign (weak0, weak1) uart_rx = 1'b1;
  assign (weak0, weak1) uart_tx = 1'b1;
  assign uart_rx = uart_if.uart_rx;
  assign uart_if.uart_tx = uart_tx;

  // TODO: USB-related signals, hookup an interface.
  assign usb_rst_n  = `USBDEV_HIER.rst_usb_48mhz_ni;
  assign usb_dp0    = 1'b1;
  assign usb_dn0    = 1'b0;
  assign usb_sense0 = 1'b0;
  assign usb_dppullup0 = 1'b0;
  assign usb_dnpullup0 = 1'b0;

  `define SIM_SRAM_IF u_sim_sram.u_sim_sram_if

  // Instantiate & connect the simulation SRAM inside the CPU (rv_core_ibex) using forces.
  sim_sram u_sim_sram (
    .clk_i    (`CPU_HIER.clk_i),
    .rst_ni   (`CPU_HIER.rst_ni),
    .tl_in_i  (`CPU_HIER.tl_d_o_int),
    .tl_in_o  (),
    .tl_out_o (),
    .tl_out_i (`CPU_HIER.tl_d_i)
  );

  initial begin
    void'($value$plusargs("en_sim_sram=%0b", en_sim_sram));
    if (!stub_cpu && en_sim_sram) begin
      `SIM_SRAM_IF.start_addr = SW_DV_START_ADDR;
      force `CPU_HIER.tl_d_i_int = u_sim_sram.tl_in_o;
      force `CPU_HIER.tl_d_o = u_sim_sram.tl_out_o;
    end else begin
      force u_sim_sram.clk_i = 1'b0;
    end
  end

  // Bind the SW test status interface directly to the sim SRAM interface.
  bind `SIM_SRAM_IF sw_test_status_if u_sw_test_status_if (
    .addr (tl_h2d.a_address),
    .data (tl_h2d.a_data[15:0]),
    .*
  );

  // Bind the SW logger interface directly to the sim SRAM interface.
  bind `SIM_SRAM_IF sw_logger_if u_sw_logger_if (
    .addr (tl_h2d.a_address),
    .data (tl_h2d.a_data),
    .*
  );

  // connect alert rx/tx to alert_if
  for (genvar k = 0; k < NUM_ALERTS; k++) begin : gen_connect_alerts_pins
    assign alert_if[k].alert_rx = `ALERT_HANDLER_HIER.alert_rx_o[k];
    initial begin
      uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.m_alert_agent_%0s",
          LIST_OF_ALERTS[k]), "vif", alert_if[k]);
    end
  end : gen_connect_alerts_pins

  initial begin
    // Set clk_rst_vifs
    // drive rst_n from clk_if
    // clk_rst_if references internal clock created by ast
    clk_rst_if.set_active();
    usb_clk_rst_if.set_active(.drive_clk_val(1'b1), .drive_rst_n_val(1'b0));
    // clk_rst_if will be gotten by env and env.scoreboard (for xbar)
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "usb_clk_rst_vif", usb_clk_rst_if);

    // IO Interfaces
    uvm_config_db#(virtual pins_if #(NUM_GPIOS))::set(null, "*.env", "gpio_vif", gpio_if);
    uvm_config_db#(virtual uart_if)::set(null, "*.env.m_uart_agent*", "vif", uart_if);
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_agent*", "vif", jtag_if);
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", cpu_d_tl_if);

    // Strap pins
    uvm_config_db#(virtual pins_if #(1))::set(
        null, "*.env", "srst_n_vif", srst_n_if);
    uvm_config_db#(virtual pins_if #(1))::set(
        null, "*.env", "jtag_spi_n_vif", jtag_spi_n_if);
    uvm_config_db#(virtual pins_if #(1))::set(
        null, "*.env", "bootstrap_vif", bootstrap_if);
    uvm_config_db#(virtual pins_if #(1))::set(
        null, "*.env", "rst_n_mon_vif", rst_n_mon_if);

    // Backdoors
    uvm_config_db#(mem_bkdr_vif)::set(
        null, "*.env", "rom_bkdr_vif", `ROM_HIER.rom_mem_bkdr_if);
    uvm_config_db#(parity_mem_bkdr_vif)::set(
        null, "*.env", "ram_main_bkdr_vif", `RAM_MAIN_HIER.ram_mem_bkdr_if);
    uvm_config_db#(parity_mem_bkdr_vif)::set(
        null, "*.env", "ram_ret_bkdr_vif", `RAM_RET_HIER.ram_mem_bkdr_if);
    uvm_config_db#(mem_bkdr_vif)::set(
        null, "*.env", "flash_bank0_bkdr_vif", `FLASH0_MEM_HIER.flash0_mem_bkdr_if);
    uvm_config_db#(mem_bkdr_vif)::set(
        null, "*.env", "flash_bank1_bkdr_vif", `FLASH1_MEM_HIER.flash1_mem_bkdr_if);
    uvm_config_db#(mem_bkdr_vif)::set(
        null, "*.env", "flash_info0_bkdr_vif", `FLASH0_INFO_HIER.flash0_info_bkdr_if);
    uvm_config_db#(mem_bkdr_vif)::set(
        null, "*.env", "flash_info1_bkdr_vif", `FLASH1_INFO_HIER.flash1_info_bkdr_if);
    uvm_config_db#(ecc_mem_bkdr_vif)::set(
        null, "*.env", "otp_bkdr_vif", `OTP_MEM_HIER.otp_bkdr_if);

    // SW logger and test status interfaces.
    uvm_config_db#(virtual sw_test_status_if)::set(
        null, "*.env", "sw_test_status_vif", `SIM_SRAM_IF.u_sw_test_status_if);
    uvm_config_db#(virtual sw_logger_if)::set(
        null, "*.env", "sw_logger_vif", `SIM_SRAM_IF.u_sw_logger_if);

    // temp disable pinmux assertion AonWkupReqKnownO_A because driving X in spi_device.sdi and
    // WkupPadSel choose IO_DPS1 in MIO will trigger this assertion
    // TODO: remove this assertion once pinmux is templatized
    $assertoff(0, dut.top_earlgrey.u_pinmux_aon.AonWkupReqKnownO_A);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  `undef SIM_SRAM_IF

  // stub cpu environment
  // if enabled, clock to cpu is forced to 0
  // cpu_d_tl_if force are applied to cpu d tl interface
  initial begin
    void'($value$plusargs("stub_cpu=%0b", stub_cpu));
    if (stub_cpu) begin
      force `CPU_HIER.clk_i = 1'b0;
      force `CPU_HIER.tl_d_o = cpu_d_tl_if.h2d;
    end else begin
      force cpu_d_tl_if.h2d = `CPU_HIER.tl_d_o;
    end
  end
  assign cpu_d_tl_if.d2h = `CPU_HIER.tl_d_i;

  // otp test_access memory is only accessible after otp_init and lc_dft_en = 1.
  // TODO: remove them once the otp/pwr otp/lc connections are completed.
  initial begin
    string common_seq_type, csr_seq_type;
    void'($value$plusargs("run_%0s", common_seq_type));
    void'($value$plusargs("csr_%0s", csr_seq_type));
    if (common_seq_type inside {"mem_partial_access", "csr_mem_rw_with_rand_reset", "tl_errors"} ||
        csr_seq_type == "mem_walk") begin
      force tb.dut.top_earlgrey.u_otp_ctrl.lc_dft_en_i = 4'b1010;
    end
  end

  // Control assertions in the DUT with UVM resource string "dut_assert_en".
  `DV_ASSERT_CTRL("dut_assert_en", tb.dut)

  `include "../autogen/tb__xbar_connect.sv"
  `include "../autogen/tb__alert_handler_connect.sv"

endmodule
