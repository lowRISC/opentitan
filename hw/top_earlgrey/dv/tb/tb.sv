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

  // backdoors
  bind `ROM_HIER mem_bkdr_if rom_mem_bkdr_if();
  bind `RAM_MAIN_HIER mem_bkdr_if ram_mem_bkdr_if();
  bind `RAM_RET_HIER mem_bkdr_if ram_mem_bkdr_if();
  bind `FLASH0_MEM_HIER mem_bkdr_if flash0_mem_bkdr_if();
  bind `FLASH1_MEM_HIER mem_bkdr_if flash1_mem_bkdr_if();
  bind `FLASH0_INFO_HIER mem_bkdr_if flash0_info_bkdr_if();
  bind `FLASH1_INFO_HIER mem_bkdr_if flash1_info_bkdr_if();
  bind `OTP_MEM_HIER mem_bkdr_if otp_bkdr_if();

  top_earlgrey_asic dut (
    // Clock and Reset
    .IO_CLK           (clk),
    .IO_RST_N         (rst_n),
    .IO_CLK_USB_48MHZ (usb_clk),

    // JTAG / SPI interface
    .IO_DPS0          (io_dps[0]),
    .IO_DPS1          (io_dps[1]),
    .IO_DPS2          (io_dps[2]),
    .IO_DPS3          (io_dps[3]),
    .IO_DPS4          (io_dps[4]),
    .IO_DPS5          (io_dps[5]),
    .IO_DPS6          (io_dps[6]),
    .IO_DPS7          (io_dps[7]),

    // UART interface
    .IO_URX           (uart_rx),
    .IO_UTX           (uart_tx),

    // USB interface
    .IO_USB_DP0       (usb_dp0),
    .IO_USB_DN0       (usb_dn0),
    .IO_USB_SENSE0    (usb_sense0),
    .IO_USB_DNPULLUP0 (usb_dppullup0),
    .IO_USB_DPPULLUP0 (usb_dnpullup0),

    // GPIO x 16 interface
    .IO_GP0           (gpio_pins[0 ]),
    .IO_GP1           (gpio_pins[1 ]),
    .IO_GP2           (gpio_pins[2 ]),
    .IO_GP3           (gpio_pins[3 ]),
    .IO_GP4           (gpio_pins[4 ]),
    .IO_GP5           (gpio_pins[5 ]),
    .IO_GP6           (gpio_pins[6 ]),
    .IO_GP7           (gpio_pins[7 ]),
    .IO_GP8           (gpio_pins[8 ]),
    .IO_GP9           (gpio_pins[9 ]),
    .IO_GP10          (gpio_pins[10]),
    .IO_GP11          (gpio_pins[11]),
    .IO_GP12          (gpio_pins[12]),
    .IO_GP13          (gpio_pins[13]),
    .IO_GP14          (gpio_pins[14]),
    .IO_GP15          (gpio_pins[15])
  );

  // connect signals
  assign io_dps[0]  = jtag_spi_n ? jtag_tck : spi_device_sck;
  assign io_dps[1]  = jtag_spi_n ? jtag_tdi : spi_device_sdi_i;
  assign io_dps[3]  = jtag_spi_n ? jtag_tms : spi_device_csb;
  assign io_dps[4]  = jtag_trst_n;
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
  assign spi_device_sdi_i   = spi_if.sdi;
  assign spi_if.sdo         = spi_device_sdo_o;

  assign uart_rx = uart_if.uart_rx;
  assign uart_if.uart_tx = uart_tx;

  // TODO: USB-related signals, hookup an interface.
  assign usb_rst_n  = `USBDEV_HIER.rst_usb_48mhz_ni;
  assign usb_dp0    = 1'b1;
  assign usb_dn0    = 1'b0;
  assign usb_sense0 = 1'b0;

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
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[Rom]", `ROM_HIER.rom_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[RamMain]", `RAM_MAIN_HIER.ram_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[RamRet]", `RAM_RET_HIER.ram_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[FlashBank0]", `FLASH0_MEM_HIER.flash0_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[FlashBank1]", `FLASH1_MEM_HIER.flash1_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[FlashBank0Info]", `FLASH0_INFO_HIER.flash0_info_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[FlashBank1Info]", `FLASH1_INFO_HIER.flash1_info_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(
        null, "*.env", "mem_bkdr_vifs[Otp]", `OTP_MEM_HIER.otp_bkdr_if);

    // SW logger and test status interfaces.
    uvm_config_db#(virtual sw_test_status_if)::set(
        null, "*.env", "sw_test_status_vif", `SIM_SRAM_IF.u_sw_test_status_if);
    uvm_config_db#(virtual sw_logger_if)::set(
        null, "*.env", "sw_logger_vif", `SIM_SRAM_IF.u_sw_logger_if);

    // temp disable pinmux assertion AonWkupReqKnownO_A because driving X in spi_device.sdi and
    // WkupPadSel choose IO_DPS1 in MIO will trigger this assertion
    // TODO: remove this assertion once pinmux is templatized
    $assertoff(0, dut.top_earlgrey.u_pinmux.AonWkupReqKnownO_A);

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
    if (common_seq_type inside {"mem_partial_access", "tl_errors"} ||
        csr_seq_type == "mem_walk") begin
      force tb.dut.top_earlgrey.u_otp_ctrl.lc_dft_en_i = 4'b1010;
    end
  end

  // Control assertions in the DUT with UVM resource string "dut_assert_en".
  `DV_ASSERT_CTRL("dut_assert_en", tb.dut)

  `include "../autogen/tb__xbar_connect.sv"
  `include "../autogen/tb__alert_handler_connect.sv"

endmodule
