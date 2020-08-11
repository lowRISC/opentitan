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

  // internal clocks and resets
  // cpu clock cannot reference cpu_hier since cpu clocks are forced off in stub_cpu mode
  wire cpu_clk = `CLKMGR_HIER.clocks_o.clk_proc_main;
  wire cpu_rst_n = `CPU_HIER.rst_ni;

  // interfaces
  clk_rst_if clk_rst_if (
      .clk,
      .rst_n
  );
  clk_rst_if usb_clk_rst_if (
      .clk  (usb_clk),
      .rst_n(usb_rst_n)
  );
  pins_if #(NUM_GPIOS) gpio_if (.pins(gpio_pins));
  pins_if #(1) srst_n_if (.pins(srst_n));
  pins_if #(1) jtag_spi_n_if (.pins(jtag_spi_n));
  pins_if #(1) bootstrap_if (.pins(bootstrap));
  pins_if #(1) rst_n_mon_if (.pins(cpu_rst_n));
  spi_if spi_if (.rst_n);
  tl_if cpu_d_tl_if (
      .clk  (cpu_clk),
      .rst_n(cpu_rst_n)
  );
  uart_if uart_if ();
  jtag_if jtag_if ();

  // backdoors
  bind `ROM_HIER mem_bkdr_if rom_mem_bkdr_if ();
  bind `RAM_MAIN_SUB_HIER mem_bkdr_if ram_mem_bkdr_if ();
  bind `FLASH0_MEM_HIER mem_bkdr_if flash0_mem_bkdr_if ();
  bind `FLASH1_MEM_HIER mem_bkdr_if flash1_mem_bkdr_if ();

  top_earlgrey_asic dut (
      // Clock and Reset
      .IO_CLK          (clk),
      .IO_RST_N        (rst_n),
      .IO_CLK_USB_48MHZ(usb_clk),

      // JTAG / SPI interface
      .IO_DPS0(io_dps[0]),
      .IO_DPS1(io_dps[1]),
      .IO_DPS2(io_dps[2]),
      .IO_DPS3(io_dps[3]),
      .IO_DPS4(io_dps[4]),
      .IO_DPS5(io_dps[5]),
      .IO_DPS6(io_dps[6]),
      .IO_DPS7(io_dps[7]),

      // UART interface
      .IO_URX(uart_rx),
      .IO_UTX(uart_tx),

      // USB interface
      .IO_USB_DP0      (usb_dp0),
      .IO_USB_DN0      (usb_dn0),
      .IO_USB_SENSE0   (usb_sense0),
      .IO_USB_DNPULLUP0(usb_dppullup0),
      .IO_USB_DPPULLUP0(usb_dnpullup0),

      // GPIO x 16 interface
      .IO_GP0 (gpio_pins[0]),
      .IO_GP1 (gpio_pins[1]),
      .IO_GP2 (gpio_pins[2]),
      .IO_GP3 (gpio_pins[3]),
      .IO_GP4 (gpio_pins[4]),
      .IO_GP5 (gpio_pins[5]),
      .IO_GP6 (gpio_pins[6]),
      .IO_GP7 (gpio_pins[7]),
      .IO_GP8 (gpio_pins[8]),
      .IO_GP9 (gpio_pins[9]),
      .IO_GP10(gpio_pins[10]),
      .IO_GP11(gpio_pins[11]),
      .IO_GP12(gpio_pins[12]),
      .IO_GP13(gpio_pins[13]),
      .IO_GP14(gpio_pins[14]),
      .IO_GP15(gpio_pins[15])
  );

  // connect sw_logger_if
  bit sw_log_valid;
  bit [TL_AW-1:0] sw_log_addr;

  sw_logger_if sw_logger_if (
      .clk        (`RAM_MAIN_SUB_HIER.clk_i),
      .rst_n      (`RAM_MAIN_HIER.rst_ni),
      .valid      (sw_log_valid),
      .addr_data  (`RAM_MAIN_SUB_HIER.wdata_i),
      .sw_log_addr(sw_log_addr)
  );
  assign sw_log_valid = !stub_cpu && `RAM_MAIN_SUB_HIER.req_i && `RAM_MAIN_SUB_HIER.write_i &&
  /* RAM only looks at the 14-bit word address 15:2 */
  (`RAM_MAIN_SUB_HIER.addr_i == sw_log_addr[15:2]);

  // connect the sw_test_status_if
  sw_test_status_if sw_test_status_if ();
  assign sw_test_status_if.valid =
      !stub_cpu && `RAM_MAIN_SUB_HIER.req_i && `RAM_MAIN_SUB_HIER.write_i && (
      `RAM_MAIN_SUB_HIER.addr_i == sw_test_status_if.sw_test_status_addr[15:2]);
  assign sw_test_status_if.sw_test_status_val = `RAM_MAIN_SUB_HIER.wdata_i;

  // connect signals
  assign io_dps[0] = jtag_spi_n ? jtag_tck : spi_device_sck;
  assign io_dps[1] = jtag_spi_n ? jtag_tdi : spi_device_sdi_i;
  assign io_dps[3] = jtag_spi_n ? jtag_tms : spi_device_csb;
  assign io_dps[4] = jtag_trst_n;
  assign io_dps[5] = srst_n;
  assign io_dps[6] = jtag_spi_n;
  assign io_dps[7] = bootstrap;
  assign spi_device_sdo_o = jtag_spi_n ? 1'b0 : io_dps[2];
  assign jtag_tdo = jtag_spi_n ? io_dps[2] : 1'b0;

  assign jtag_tck = jtag_if.tck;
  assign jtag_tms = jtag_if.tms;
  assign jtag_trst_n = jtag_if.trst_n;
  assign jtag_tdi = jtag_if.tdi;
  assign jtag_if.tdo = jtag_tdo;

  assign spi_device_sck = spi_if.sck;
  assign spi_device_csb = spi_if.csb;
  assign spi_device_sdi_i = spi_if.sdi;
  assign spi_if.sdo = spi_device_sdo_o;

  assign uart_rx = uart_if.uart_rx;
  assign uart_if.uart_tx = uart_tx;

  // TODO: USB-related signals, hookup an interface.
  assign usb_rst_n = `USBDEV_HIER.rst_usb_48mhz_ni;
  assign usb_dp0 = 1'b1;
  assign usb_dn0 = 1'b0;
  assign usb_sense0 = 1'b0;

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
    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "srst_n_vif", srst_n_if);
    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "jtag_spi_n_vif", jtag_spi_n_if);
    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "bootstrap_vif", bootstrap_if);
    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "rst_n_mon_vif", rst_n_mon_if);

    // Backdoors
    uvm_config_db#(virtual mem_bkdr_if)::set(null, "*.env", "mem_bkdr_vifs[Rom]",
                                             `ROM_HIER.rom_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(null, "*.env", "mem_bkdr_vifs[Ram]",
                                             `RAM_MAIN_SUB_HIER.ram_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(null, "*.env", "mem_bkdr_vifs[FlashBank0]",
                                             `FLASH0_MEM_HIER.flash0_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(null, "*.env", "mem_bkdr_vifs[FlashBank1]",
                                             `FLASH1_MEM_HIER.flash1_mem_bkdr_if);

    // SW logger and test status interfaces.
    uvm_config_db#(virtual sw_logger_if)::set(null, "*.env", "sw_logger_vif", sw_logger_if);
    uvm_config_db#(virtual sw_test_status_if)::set(null, "*.env", "sw_test_status_vif",
                                                   sw_test_status_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

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

  //`include "../autogen/tb__xbar_connect.sv"

endmodule
