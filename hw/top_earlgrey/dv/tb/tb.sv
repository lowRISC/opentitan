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
  import mem_bkdr_util_pkg::mem_bkdr_util;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "chip_hier_macros.svh"

  wire clk, rst_n;
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
  wire [1:0] tap_straps;
  wire [1:0] dft_straps;
  wire [2:0] sw_straps;
  wire [7:0] io_dps;

  wire usb_dp0, usb_dn0, usb_sense0, usb_dppullup0, usb_dnpullup0;

  wire uart_rx[NUM_UARTS], uart_tx[NUM_UARTS];

  bit stub_cpu;
  bit en_sim_sram = 1'b1;

  // internal clocks and resets
  // cpu clock cannot reference cpu_hier since cpu clocks are forced off in stub_cpu mode
  wire cpu_clk = `CPU_HIER.clk_i;
  wire cpu_rst_n = `CPU_HIER.rst_ni;
  wire alert_handler_clk = `ALERT_HANDLER_HIER.clk_i;
  wire alert_handler_rst_n = `ALERT_HANDLER_HIER.rst_ni;

  // interfaces
  clk_rst_if clk_rst_if(.clk, .rst_n);
  alert_esc_if alert_if[NUM_ALERTS](.clk(alert_handler_clk), .rst_n(alert_handler_rst_n));
  pins_if #(NUM_GPIOS) gpio_if(.pins(gpio_pins));
  pins_if #(1) srst_n_if(.pins(srst_n));
  pins_if #(2) tap_straps_if(.pins(tap_straps));
  pins_if #(2) dft_straps_if(.pins(dft_straps));
  pins_if #(3) sw_straps_if(.pins(sw_straps));
  pins_if #(1) rst_n_mon_if(.pins(cpu_rst_n));
  spi_if spi_if(.rst_n);
  tl_if cpu_d_tl_if(.clk(cpu_clk), .rst_n(cpu_rst_n));
  uart_if uart_if[NUM_UARTS-1:0]();
  jtag_if jtag_if();

  bind dut ast_supply_if ast_supply_if (
    .clk(top_earlgrey.clk_aon_i),
    .trigger(top_earlgrey.rv_core_ibex_pwrmgr.core_sleeping)
  );

  // TODO: Replace with correct interfaces once
  // pinmux/padring and pinout have been updated.
  wire [24:0] tie_off;
  wire [5:0] spi_host_tie_off;
  wire [1:0] spi_dev_tie_off;
  assign (weak0, weak1) tie_off = '0;
  assign (weak0, weak1) spi_host_tie_off = '0;
  assign (weak0, weak1) spi_dev_tie_off = '0;

  // TODO: the external clk is currently not connected.
  // We will need to feed this in via a muxed pin, once that function implemented.

  chip_earlgrey_asic dut (
    // Clock and Reset (VCC domain)
    .POR_N(rst_n),
    // Dedicated SPI Host (VIOA domain)
    .SPI_HOST_D0(spi_host_tie_off[0]),
    .SPI_HOST_D1(spi_host_tie_off[1]),
    .SPI_HOST_D2(spi_host_tie_off[2]),
    .SPI_HOST_D3(spi_host_tie_off[3]),
    .SPI_HOST_CLK(spi_host_tie_off[4]),
    .SPI_HOST_CS_L(spi_host_tie_off[5]),
    // Dedicated SPI Device (VIOA domain)
    .SPI_DEV_D0(spi_device_sdi_i),
    .SPI_DEV_D1(spi_device_sdo_o),
    .SPI_DEV_D2(spi_dev_tie_off[0]),
    .SPI_DEV_D3(spi_dev_tie_off[1]),
    .SPI_DEV_CLK(spi_device_sck),
    .SPI_DEV_CS_L(spi_device_csb),
    // Bank A (VIOA domain)
    .IOA0(gpio_pins[0]),   // MIO 0
    .IOA1(gpio_pins[1]),   // MIO 1
    .IOA2(gpio_pins[2]),   // MIO 2
    .IOA3(gpio_pins[3]),   // MIO 3
    .IOA4(gpio_pins[4]),   // MIO 4
    .IOA5(gpio_pins[5]),   // MIO 5
    .IOA6(gpio_pins[6]),   // MIO 6
    .IOA7(gpio_pins[7]),   // MIO 7
    .IOA8(gpio_pins[8]),   // MIO 8
    // Bank B (VIOB domain)
    .IOB0(gpio_pins[9]),   // MIO 9
    .IOB1(gpio_pins[10]),  // MIO 10
    .IOB2(gpio_pins[11]),  // MIO 11
    .IOB3(gpio_pins[12]),  // MIO 12
    .IOB4(gpio_pins[13]),  // MIO 13
    .IOB5(gpio_pins[14]),  // MIO 14
    .IOB6(gpio_pins[15]),  // MIO 15
    .IOB7(tie_off[0]),     // MIO 16
    // TODO, we probably need to change this when we have the final pinout configuration
    // Connect this to IOB8 to align with SW bootstrap.c
    .IOB8(sw_straps[0]),   // MIO 17
    .IOB9(tie_off[1]),     // MIO 18
    .IOB10(tie_off[2]),    // MIO 19
    .IOB11(tie_off[3]),    // MIO 20
    .IOB12(tie_off[4]),    // MIO 21
    // Bank C (VCC domain)
    .IOC0(tie_off[5]),     // MIO 22
    .IOC1(sw_straps[1]),   // MIO 23
    .IOC2(sw_straps[2]),   // MIO 24
    .IOC3(dft_straps[0]),  // MIO 25
    .IOC4(dft_straps[1]),  // MIO 26
    .IOC5(tap_straps[1]),  // MIO 27
    .IOC6(clk),            // MIO 28 - external clock fed in at a fixed position
    .IOC7(tie_off[7]),     // MIO 29
    .IOC8(tap_straps[0]),  // MIO 30
    .IOC9(tie_off[8]),     // MIO 31
    .IOC10(uart_rx[0]),    // MIO 32
    .IOC11(uart_tx[0]),    // MIO 33
    .IOC12(tie_off[9]),    // MIO 34
    // Bank R (VCC domain)
    .IOR0(jtag_tms),       // MIO 35
    .IOR1(jtag_tdo),       // MIO 36
    .IOR2(jtag_tdi),       // MIO 37
    .IOR3(jtag_tck),       // MIO 38
    .IOR4(jtag_trst_n),    // MIO 39
    .IOR5(uart_rx[1]),     // MIO 40
    .IOR6(uart_tx[1]),     // MIO 41
    .IOR7(uart_rx[2]),     // MIO 42
    .IOR8(tie_off[13]),    // MIO 43, Dedicated sysrst_ctrl output (ec_rst_l)
    .IOR9(tie_off[14]),    // MIO 44, Dedicated sysrst_ctrl output (pwrb_out)
    .IOR10(uart_tx[2]),    // MIO 45
    .IOR11(uart_rx[3]),    // MIO 46
    .IOR12(uart_tx[3]),    // MIO 47
    .IOR13(tie_off[18]),   // MIO 48
    // DCD (VCC domain)
    .CC1(tie_off[19]),
    .CC2(tie_off[20]),
    // USB (VCC domain)
    .USB_P(usb_dp0),
    .USB_N(usb_dn0),
    // FLASH
    .FLASH_TEST_MODE0(tie_off[21]),
    .FLASH_TEST_MODE1(tie_off[22]),
    .FLASH_TEST_VOLT(tie_off[23]),
    // MISC pad
    .AST_MISC(tie_off[24])
  );

  // connect signals
  // TODO: Replace this weak pull to a known value with initialization
  // in the agent/interface.
  // Without these pulls, we may get Xes that propagate through the design
  // (one example is the interference IRQ of the I2C that propagates into the PLIC).
  assign (weak0, weak1) jtag_tck = 1'b0;
  assign (weak0, weak1) jtag_tms = 1'b0;
  assign (weak0, weak1) jtag_trst_n = 1'b0;
  assign (weak0, weak1) jtag_tdi = 1'b0;
  assign (weak0, weak1) jtag_tdo = 1'b0;
  assign jtag_tck         = jtag_if.tck;
  assign jtag_tms         = jtag_if.tms;
  assign jtag_trst_n      = jtag_if.trst_n;
  assign jtag_tdi         = jtag_if.tdi;
  assign jtag_if.tdo      = jtag_tdo;

  assign spi_device_sck   = spi_if.sck;
  assign spi_device_csb   = spi_if.csb;
  assign spi_device_sdi_i = spi_if.sio[0];
  assign spi_if.sio[1]    = spi_device_sdo_o;

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
    .tl_out_i (`CPU_HIER.cored_tl_h_i)
  );

  initial begin
    void'($value$plusargs("en_sim_sram=%0b", en_sim_sram));
    if (!stub_cpu && en_sim_sram) begin
      `SIM_SRAM_IF.start_addr = SW_DV_START_ADDR;
      force `CPU_HIER.tl_d_i_int = u_sim_sram.tl_in_o;
      force `CPU_HIER.cored_tl_h_o = u_sim_sram.tl_out_o;
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
    // Set clk_rst_vifs.
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", clk_rst_if);

    // IO Interfaces
    uvm_config_db#(virtual pins_if #(NUM_GPIOS))::set(null, "*.env", "gpio_vif", gpio_if);
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_riscv_agent*", "vif", jtag_if);
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", cpu_d_tl_if);

    // Strap pins
    uvm_config_db#(virtual pins_if #(2))::set(
        null, "*.env", "tap_straps_vif", tap_straps_if);
    uvm_config_db#(virtual pins_if #(2))::set(
        null, "*.env", "dft_straps_vif", dft_straps_if);
    uvm_config_db#(virtual pins_if #(3))::set(
        null, "*.env", "sw_straps_vif", sw_straps_if);
    uvm_config_db#(virtual pins_if #(1))::set(
        null, "*.env", "rst_n_mon_vif", rst_n_mon_if);

    // SW logger and test status interfaces.
    uvm_config_db#(virtual sw_test_status_if)::set(
        null, "*.env", "sw_test_status_vif", `SIM_SRAM_IF.u_sw_test_status_if);
    uvm_config_db#(virtual sw_logger_if)::set(
        null, "*.env", "sw_logger_vif", `SIM_SRAM_IF.u_sw_logger_if);

    // AST supply interface.
    uvm_config_db#(virtual ast_supply_if)::set(
        null, "*.env", "ast_supply_vif", dut.ast_supply_if);

    // temp disable pinmux assertion AonWkupReqKnownO_A because driving X in spi_device.sdi and
    // WkupPadSel choose IO_DPS1 in MIO will trigger this assertion
    // TODO: remove this assertion once pinmux is templatized
    $assertoff(0, dut.top_earlgrey.u_pinmux_aon.AonWkupReqKnownO_A);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  for (genvar i = 0; i < NUM_UARTS; i++) begin : gen_uart_if
    // TODO: Replace this weak pull to a known value with initialization
    // in the agent/interface.
    assign (weak0, weak1) uart_rx[i] = 1'b1;
    assign (weak0, weak1) uart_tx[i] = 1'b1;
    assign uart_rx[i] = uart_if[i].uart_rx;
    assign uart_if[i].uart_tx = uart_tx[i];

    initial begin
      uvm_config_db#(virtual uart_if)::set(null, $sformatf("*.env.m_uart_agent%0d*", i),
                                           "vif", uart_if[i]);
    end
  end
  `undef SIM_SRAM_IF

  // Instantitate the memory backdoor util instances.
  if (`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin : gen_generic
    initial begin
      mem_bkdr_util m_mem_bkdr_util[chip_mem_e];

      `uvm_info("tb.sv", "Backdoor init flash 0 data", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank0Data] = new(
          .name  ("mem_bkdr_util[FlashBank0Data]"),
          .path  (`DV_STRINGIFY(`FLASH0_DATA_MEM_HIER)),
          .depth ($size(`FLASH0_DATA_MEM_HIER)),
          .n_bits($bits(`FLASH0_DATA_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_72_64));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank0Data], `FLASH0_DATA_MEM_HIER)

      `uvm_info("tb.sv", "Backdoor init flash 0 info", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank0Info] = new(
          .name  ("mem_bkdr_util[FlashBank0Info]"),
          .path  (`DV_STRINGIFY(`FLASH0_INFO_MEM_HIER)),
          .depth ($size(`FLASH0_INFO_MEM_HIER)),
          .n_bits($bits(`FLASH0_INFO_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_72_64));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank0Info], `FLASH0_INFO_MEM_HIER)

      `uvm_info("tb.sv", "Backdoor init flash 1 data", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank1Data] = new(
          .name  ("mem_bkdr_util[FlashBank1Data]"),
          .path  (`DV_STRINGIFY(`FLASH1_DATA_MEM_HIER)),
          .depth ($size(`FLASH1_DATA_MEM_HIER)),
          .n_bits($bits(`FLASH1_DATA_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_72_64));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank1Data], `FLASH0_DATA_MEM_HIER)

      `uvm_info("tb.sv", "Backdoor init flash 0 info", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank1Info] = new(
          .name  ("mem_bkdr_util[FlashBank1Info]"),
          .path  (`DV_STRINGIFY(`FLASH1_INFO_MEM_HIER)),
          .depth ($size(`FLASH1_INFO_MEM_HIER)),
          .n_bits($bits(`FLASH1_INFO_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_72_64));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank1Info], `FLASH1_INFO_MEM_HIER)

      `uvm_info("tb.sv", "Backdoor init OTP", UVM_MEDIUM)
      m_mem_bkdr_util[Otp] = new(.name  ("mem_bkdr_util[Otp]"),
                                 .path  (`DV_STRINGIFY(`OTP_MEM_HIER)),
                                 .depth ($size(`OTP_MEM_HIER)),
                                 .n_bits($bits(`OTP_MEM_HIER)),
                                 .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_22_16));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[Otp], `OTP_MEM_HIER)

      `uvm_info("tb.sv", "Backdoor init RAM", UVM_MEDIUM)
      m_mem_bkdr_util[RamMain0] = new(.name  ("mem_bkdr_util[RamMain0]"),
                                      .path  (`DV_STRINGIFY(`RAM_MAIN_MEM_HIER)),
                                      .depth ($size(`RAM_MAIN_MEM_HIER)),
                                      .n_bits($bits(`RAM_MAIN_MEM_HIER)),
                                      .err_detection_scheme(mem_bkdr_util_pkg::ParityOdd));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamMain0], `RAM_MAIN_MEM_HIER)

      `uvm_info("tb.sv", "Backdoor init RAM RET", UVM_MEDIUM)
      m_mem_bkdr_util[RamRet0] = new(.name  ("mem_bkdr_util[RamRet0]"),
                                     .path  (`DV_STRINGIFY(`RAM_RET_MEM_HIER)),
                                     .depth ($size(`RAM_RET_MEM_HIER)),
                                     .n_bits($bits(`RAM_RET_MEM_HIER)),
                                     .err_detection_scheme(mem_bkdr_util_pkg::ParityOdd));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamRet0], `RAM_RET_MEM_HIER)

      `uvm_info("tb.sv", "Backdoor init ROM", UVM_MEDIUM)
      m_mem_bkdr_util[Rom] = new(.name  ("mem_bkdr_util[Rom]"),
                                 .path  (`DV_STRINGIFY(`ROM_MEM_HIER)),
                                 .depth ($size(`ROM_MEM_HIER)),
                                 .n_bits($bits(`ROM_MEM_HIER)),
                                 .err_detection_scheme(mem_bkdr_util_pkg::Ecc_39_32));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[Rom], `ROM_MEM_HIER)

      for (chip_mem_e mem = mem.first(), int i = 0; i < mem.num(); mem = mem.next(), i++) begin
        if (mem inside {[RamMain1:RamMain15]}) continue;
        if (mem inside {[RamRet1:RamRet15]}) continue;
        uvm_config_db#(mem_bkdr_util)::set(
            null, "*.env", m_mem_bkdr_util[mem].get_name(), m_mem_bkdr_util[mem]);
      end

    end
  end

  // stub cpu environment
  // if enabled, clock to cpu is forced to 0
  // cpu_d_tl_if force are applied to cpu d tl interface
  initial begin
    void'($value$plusargs("stub_cpu=%0b", stub_cpu));
    if (stub_cpu) begin
      // silence the main cpu clock to ensure there are no transactions.
      // also silence the translation modules as they contain arbiters
      // that are unhappy with X's, which can happen if csr_rw happens to
      // hit the right register during testing.
      // We cannot kill all clocks to CPU_CORE because the DV hijack point
      // is in front of a FIFO, so potentially this can kill transactions
      // being buffered.
      force `CPU_CORE_HIER.clk_i = 1'b0;
      force `CPU_HIER.u_ibus_trans.rst_ni = 1'b0;
      force `CPU_HIER.u_dbus_trans.rst_ni = 1'b0;
      // tl type is used to calculate ECC and we use DataType for cpu data interface
      force cpu_d_tl_if.h2d.a_user.instr_type = prim_mubi_pkg::MuBi4False;
      force `CPU_TL_ADAPT_D_HIER.tl_out = cpu_d_tl_if.h2d;
      force cpu_d_tl_if.d2h = `CPU_TL_ADAPT_D_HIER.tl_i;
    end else begin
      // when en_sim_sram == 1, need to make sure the access to sim_sram doesn't appear on
      // cpu_d_tl_if, otherwise, we may have unmapped access as scb doesn't regnize addresses of
      // sim_sram. `CPU_HIER.tl_d_* is the right place to avoid seeing sim_sram accesses
      force cpu_d_tl_if.h2d = `CPU_HIER.cored_tl_h_o;
      force cpu_d_tl_if.d2h = `CPU_HIER.cored_tl_h_i;
    end
  end

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
