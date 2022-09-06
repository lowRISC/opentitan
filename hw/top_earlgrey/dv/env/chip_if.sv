// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// One chip level interface to rule them all, and in the IOs, bind them...
//
// The top_earlgrey SoC provides a bunch of fixed-function and muxed IO pads. The interface serves
// as the gateway connection between the chip IOs and ALL functions mapped to the fixed and muxed
// IOs. It creates sub-interfaces for all functions and connects them all to the chip IOs together.
// The pin mapping to each function is provided in the following spreadsheet:
// https://docs.google.com/spreadsheets/d/1jp-paagh2_sJFMUFnewx0XAUmLdCCgXn8NnB2BNEk-Q
//
// All functional interfaces are internally (or externally, in this interface) gated off from
// driving the IOs at the same time. Since there are more functions than IOs, it is the test
// writer's responsibility to ensure that multiple functions that use the same IOs are not active at
// the same time. This interface provides an X-detection logic on all IOs to ensure there are no
// multiple drivers.
//
// This interface MUST be bound to the chip level DUT, since it references the DUT-internal signals
// via partial hierarchical paths.
interface chip_if;

  import chip_common_pkg::*;
  import dv_utils_pkg::*;
  import uvm_pkg::*;

  `include "dv_macros.svh"
  `include "uvm_macros.svh"

  // TODO: Move these to `include "chip_hier_macros.svh".
`define TOP_HIER            top_earlgrey
`define ALERT_HANDLER_HIER  `TOP_HIER.u_alert_handler
`define CPU_HIER            `TOP_HIER.u_rv_core_ibex
`define LC_CTRL_HIER        `TOP_HIER.u_lc_ctrl
`define PWM_HIER            `TOP_HIER.u_pwm
`define RSTMGR_HIER         `TOP_HIER.u_rstmgr_aon
`define USBDEV_HIER         `TOP_HIER.u_usbdev

  // Identifier for logs.
   string MsgId = $sformatf("%m");

  // Directly connected to chip IOs.
  //
  // DO NOT manipulate this signal in test sequences directly. Use the individual functional
  // interfaces below instead.
  wire [IoNumTotal-1:0] ios;

  // Functional interface: for testing ALL chip IOs, such as pinmux and padctrl tests.
  pins_if#(.Width(IoNumTotal), .PullStrength("Weak")) ios_if(.pins(ios));

  // Weak pulls for each pad pin.
  //
  // All ios are weak-pulled by default. The test sequences disable the pull by "enabling" the IO
  // functionality that is being tested.
  initial begin
    // Enable weak pulldown on most signals.
    ios_if.pins_pd = '1;
    ios_if.pins_pd[PorN] = 0;
    ios_if.pins_pd[UsbP] = 0;
    ios_if.pins_pd[IoR8] = 0;
    ios_if.pins_pd[IoR9] = 0;
    // Chip outputs.
    ios_if.pins_pd[SpiHostCsL] = 0;
    ios_if.pins_pd[SpiHostClk] = 0;
    // These are weak pullups.
    ios_if.pins_pu[PorN] = 1;
    ios_if.pins_pu[UsbP] = 1;
    ios_if.pins_pu[IoR8] = 1;
    ios_if.pins_pu[IoR9] = 1;
    ios_if.pins_pd[PorN] = 0;
  end

  // Unknown monitor on chip IOs.
  //
  // Chip IOs must always either be undriven or driven to a known value. Xs indicate multiple
  // drivers, which is an issue likely caused by multiple functions simultaneously attempting to
  // control the shared (muxed) pads.
  initial begin
    foreach (ios[i]) begin
      fork
        forever @(ios[i]) begin
          automatic int a_i = i;
          automatic chip_io_e io = chip_io_e'(a_i);
          `DV_CHECK_FATAL(ios[a_i] !== 1'bx,
                          $sformatf("Possible multiple drivers on chip IO %0s", io.name()), MsgId)
        end
      join_none
    end
  end

  // Functional interfaces.
  //
  // The section below creates functional interfaces and connects the signals to the `ios` wires.
  // Depending on the type of the IO, the following signaling choices are made:
  //
  // - Dedicated IOs with fixed direction (either input or output):
  //   - Create `logic` or equivalent data type signals to drive inputs / sample outputs.
  //
  // - Dedicated IOs that are bidirectional (inouts):
  //   - Create pins_if instance, since it internally has direction controls.
  //
  // - Muxed IOs:
  //   - Create pins_if instance, since it internally has direction controls.
  //
  // - IO peripheral interfaces:
  //   - Create the corresponding IO interface, such as uart_if.
  //   - Ideally, the interface agent must internally provide direction control, especially for
  //     signals driven into the chip.
  //   - If that is infeasible, then create a control signal locally.
  //
  // - Internal probes and forces:
  //   - Create `logic` or equivalent data type signals, or create the UVM agent interfaces.
  //
  // On the muxed IOs, multiple functional interfaces are connected to the same `ios` wires. A
  // single `ios` wire cannot be driven by more than one function at the same time. This must be
  // handled properly by the test sequence, which will enable the direction control for the required
  // interfaces based on the test's needs at the right times. By default, all chip IOs are weak
  // pulled via the chip_ios_if direction controls. If multiple drivers are found, The unknown
  // monitor above will throw a fatal error and exit the simulation.

  // Functional (dedicated) interface (input): POR_RST_N.
  logic por_n;
  assign ios[PorN] = por_n;

  // Functional (dedicated) interface (inout): USB.
  // TODO!

  // Functional (dedicated) interface (input): CC1.
  logic cc1;
  assign ios[CC1] = cc1;

  // Functional (dedicated) interface (input): CC2.
  logic cc2;
  assign ios[CC2] = cc2;

  // Functional (dedicated) interface (analog input): flash test volt.
  logic flash_test_volt;
  assign ios[CC2] = flash_test_volt;

  // Functional (dedicated) interface (input): flash test mode0.
  logic flash_test_mode0;
  assign ios[FlashTestMode0] = flash_test_mode0;

  // Functional (dedicated) interface (input): flash test mode1.
  logic flash_test_mode1;
  assign ios[FlashTestMode1] = flash_test_mode1;

  // Functional (dedicated) interface (analog input): OTP ext volt.
  logic otp_ext_volt;
  assign ios[OtpExtVolt] = otp_ext_volt;

  // Functional (dedicated) interface: SPI host interface (drives traffic into the chip).
  // spi_if spi_host_if(.rst_n(top_earlgrey.u_spi_device.rst_ni),
  //                    .sck(ios[SpiDevClk]),
  //                    .csb(ios[SpiDevCSL]),
  //                    .sio(ios[SpiDevD3:SpiDevD0]));

  // Functional (dedicated) interface: SPI AP device interface (receives traffic from the chip).
  // spi_if spi_device_ap_if(.rst_n(top_earlgrey.u_spi_host0.rst_ni));
  // assign spi_device_ap_if.csk = ios[SpiHostClk];
  // assign spi_device_ap_if.csb = ios[SpiHostCsL];
  // for (genvar i = 0; i < 4; i++) begin : gen_spi_device_ap_if_sio_conn
  //   // TODO: This logic needs to be firmed up.
  //   assign ios[SpiHostD0 + i] = spi_device_ap_if.sio_oe[i] ? spi_device_ap_if.sio[i] : 1'bz;
  //   assign spi_device_ap_if.sio[i] = ~spi_device_ap_if.sio_oe[i] ? ios[SpiHostD0 + i] : 1'bz;
  // end

  // Functional (dedicated) interface (inout): EC reset.
  pins_if #(1) ec_rst_l_if(.pins(ios[IoR8]));

  // Functional (dedicated) interface (inout): flash write protect.
  pins_if #(1) flash_wp_l_if(.pins(ios[IoR9]));

  // Functional (dedicated) interface (input): AST misc.
  logic ast_misc;
  assign ios[AstMisc] = ast_misc;

  // Functional (muxed) interface: GPIOs.
  //
  // Note: The ChromeOS pinout uses fewer GPIO pins that what is assigned below.
  pins_if #(31) gpio_pins_if(
    .pins({ios[IoA0] /* !! */, ios[IoA1] /* !! */, ios[IoA2], ios[IoA3],
           ios[IoA4] /* ** */, ios[IoA5] /* ** */, ios[IoA6], ios[IoB0],
           ios[IoB1], ios[IoB2], ios[IoB3], ios[IoB4],
           ios[IoB5], ios[IoB6], ios[IoB7], ios[IoB8],
           ios[IoC5], ios[IoC6], ios[IoC7], ios[IoC9],
           ios[IoC10], ios[IoC11], ios[IoC12], ios[IoR0],
           ios[IoR1], ios[IoR2], ios[IoR3], ios[IoR4],
           ios[IoR5], ios[IoR6], ios[IoR7]})
  );
  // !!: Pins exclusively used by UART3 (AP) in ChromeOS,  but treated as GPIOs for Enterprise.
  // **: Pins exclusively used by UART2 in both, ChromeOS and Enterprise. However, UART2 is not
  //     active in all tests, so it is ok to connect them to GPIOs.

  // Functional (muxed) interface: JTAG (valid during debug enabled LC state only).
  logic enable_jtag, debug_enabled, jtag_enabled;
  jtag_if jtag_if();

  assign debug_enabled = (`LC_CTRL_HIER.lc_hw_debug_en_o == lc_ctrl_pkg::On);
  assign jtag_enabled = enable_jtag && debug_enabled;
  assign ios[IoR0] = jtag_enabled ? jtag_if.tms : 1'bz;
  assign jtag_if.tdo = jtag_enabled ? ios[IoR1] : 1'bz;
  assign ios[IoR2] = jtag_enabled ? jtag_if.tdi : 1'bz;
  assign ios[IoR3] = jtag_enabled ? jtag_if.tck : 1'bz;
  assign ios[IoR4] = jtag_enabled ? jtag_if.trst_n : 1'bz;

  // Functional (muxed) interface: Flash controller JTAG.
  logic enable_flash_ctrl_jtag, flash_ctrl_jtag_enabled;
  jtag_if flash_ctrl_jtag_if();

  assign flash_ctrl_jtag_enabled = enable_flash_ctrl_jtag && debug_enabled;
  assign ios[IoB0] = flash_ctrl_jtag_enabled ? flash_ctrl_jtag_if.tms : 1'bz;
  assign flash_ctrl_jtag_if.tdo = flash_ctrl_jtag_enabled ? ios[IoB1] : 1'bz;
  assign ios[IoB2] = flash_ctrl_jtag_enabled ? flash_ctrl_jtag_if.tdi : 1'bz;
  assign ios[IoB3] = flash_ctrl_jtag_enabled ? flash_ctrl_jtag_if.tck : 1'bz;

  // Functional (muxed) interface: DFT straps.
  pins_if #(2) dft_straps_if(.pins(ios[IoC4:IoC3]));

  // Functional (muxed) interface: TAP straps.
  pins_if #(2) tap_straps_if(.pins({ios[IoC8], ios[IoC5]}));

  // Functional (muxed) interface: SW straps.
  pins_if #(3) sw_straps_if(.pins(ios[IoC2:IoC0]));

  // Functional (muxed) interface: AST2PAD.
  pins_if #(9) ast2pad_if(.pins({ios[IoA0], ios[IoA1], ios[IoB3], ios[IoB4],
                                 ios[IoB5], ios[IoC0], ios[IoC4], ios[IoC7],
                                 ios[IoC9]}));

  // Functional (muxed) interfas2ace: PAD2AST.
  pins_if #(8) pad2ast_if(.pins({ios[IoA4], ios[IoA5], ios[IoB0], ios[IoB1],
                                 ios[IoB2], ios[IoC1], ios[IoC2], ios[IoC3]}));

  // Functional (muxed) interface: UARTs.
  bit enable_uart[NUM_UARTS];
  uart_if uart_if[NUM_UARTS-1:0]();

  assign ios[IoC3] = enable_uart[0] ? uart_if[0].uart_rx : 1'bz;
  assign uart_if[0].uart_tx = ios[IoC4];

  assign ios[IoB4] = enable_uart[1] ? uart_if[1].uart_rx : 1'bz;
  assign uart_if[1].uart_tx = ios[IoB5];

  assign ios[IoA4] = enable_uart[2] ? uart_if[2].uart_rx : 1'bz;
  assign uart_if[2].uart_tx = ios[IoA5];

  assign ios[IoA0] = enable_uart[3] ? uart_if[3].uart_rx : 1'bz;
  assign uart_if[3].uart_tx = ios[IoA1];

  // Functional (muxed) interface: SPI EC device interface (receives traffic from the chip).
  // spi_if spi_device_ec_if(.rst_n(top_earlgrey.u_spi_host1.rst_ni));
  // assign spi_device_ec_if.csk = ios[IoB3];
  // assign spi_device_ec_if.csb = ios[IoB0];
  // assign spi_device_ec_if.sio[0] = ios[IoB1];
  // assign ios[IoB2] = assign spi_device_ec_if.sio[1] : 1'bz;

  // Functional (muxed) interface: I2Cs.
  bit enable_i2c[NUM_I2CS];
  // TODO: i2c_if i2c_if[NUM_I2CS-1:0]();

  // Functional (muxed) interface: sysrst_ctrl.
  // TODO: Replace with sysrst_ctrl IP level interface.
  // pins_if #(8) sysrst_ctrl_if();

  // Functional (muxed) interface: PWM.
  // TODO: pwm_if pwm_if[NUM_PWM_CHANNELS-1:0](
  //   .clk(`PWM_HIER.clk_i),
  //   .rst_n(`PWM_HIER.rst_ni)
  // );

  // TODO: Use the GPIO ones instead.
  // assign pwm_if[0].pwm = ios[IoB10];
  // assign pwm_if[1].pwm = ios[IoB11];
  // assign pwm_if[2].pwm = ios[IoB12];
  // assign pwm_if[3].pwm = ios[IoC10];
  // assign pwm_if[4].pwm = ios[IoB11];
  // assign pwm_if[5].pwm = ios[IoB12];

  // Functional (muxed) interface: external clock source.
  wire unused;
  clk_rst_if ext_clk_if(.clk(ios[IoC6]), .rst_n(unused));

  // Internal monitors.
  wire cpu_clk = `CPU_HIER.clk_i;
  wire cpu_rst_n = `CPU_HIER.rst_ni;
  wire alert_handler_clk = `ALERT_HANDLER_HIER.clk_i;
  wire alert_handler_rst_n = `ALERT_HANDLER_HIER.rst_ni;
  wire usb_clk = `USBDEV_HIER.clk_i;
  wire usb_rst_n = `USBDEV_HIER.rst_ni;

  // Pass interface handles to uvm_config_db.
  //
  // Since the chip_if handle itself will be passed to the chip env, there is no need to set
  // sub-interface handles that are consumed by the chip env. Only pass the sub-interface handles
  // for external interface agents.
  initial begin
    // uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_host_if);

    // uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_riscv_agent*", "vif", jtag_if);

    // foreach (uart_if[i]) begin
    //   uvm_config_db#(virtual uart_if)::set(null, $sformatf("*.env.m_uart_agent%0d*", i),
    //                                        "vif", uart_if[i]);
    // end
    // foreach (pwm_if[i]) begin
    //   uvm_config_db#(virtual pwm_if)::set(null, $sformatf("*.env.m_pwm_monitor%0d*", i),
    //                                       $sformatf("m_pwm_monitor%0d_vif", i), pwm_if[i]);
    // end

    // uvm_config_db#(virtual pins_if #(8))::set(null, "*.env", "sysrst_ctrl_vif", sysrst_ctrl_if);

  end

`undef TOP_HIER
`undef ALERT_HANDLER_HIER
`undef CPU_HIER
`undef LC_CTRL_HIER
`undef PWM_HIER
`undef RSTMGR_HIER
`undef USBDEV_HIER

endinterface
