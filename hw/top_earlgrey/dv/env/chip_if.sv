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

  // TODO: Move these to `include "./chip_hier_macros.svh". Deprecate ../tb/chip_hier_macros.svh.
  // TODO: In Xcelium, the bind is not exposing the internal hierarchies to chip_if.
`ifdef XCELIUM
  `define TOP_HIER          tb.dut.top_earlgrey
`else
  `define TOP_HIER          top_earlgrey
`endif
`define ADC_CTRL_HIER       `TOP_HIER.u_adc_ctrl_aon
`define AES_HIER            `TOP_HIER.u_aes
`define ALERT_HANDLER_HIER  `TOP_HIER.u_alert_handler
`define AON_TIMER_HIER      `TOP_HIER.u_aon_timer_aon
`define AST_HIER            u_ast
`define CLKMGR_HIER         `TOP_HIER.u_clkmgr_aon
`define CPU_HIER            `TOP_HIER.u_rv_core_ibex
`define CPU_CORE_HIER       `CPU_HIER.u_core
`define CPU_TL_ADAPT_D_HIER `CPU_HIER.tl_adapter_host_d_ibex
`define CSRNG_HIER          `TOP_HIER.u_csrng
`define ENTROPY_SRC_HIER    `TOP_HIER.u_entropy_src
`define EDN_HIER(i)         `TOP_HIER.u_edn``i
`define FLASH_CTRL_HIER     `TOP_HIER.u_flash_ctrl
`define GPIO_HIER           `TOP_HIER.u_gpio
`define HMAC_HIER           `TOP_HIER.u_hmac
`define I2C_HIER(i)         `TOP_HIER.u_i2c``i
`define KMAC_HIER           `TOP_HIER.u_kmac
`define KEYMGR_HIER         `TOP_HIER.u_keymgr
`define LC_CTRL_HIER        `TOP_HIER.u_lc_ctrl
`define OTP_CTRL_HIER       `TOP_HIER.u_otp_ctrl
`define OTBN_HIER           `TOP_HIER.u_otbn
`define PATTGEN_HIER        `TOP_HIER.u_pattgen
`define PINMUX_HIER         `TOP_HIER.u_pinmux_aon
`define PWM_HIER            `TOP_HIER.u_pwm_aon
`define PWRMGR_HIER         `TOP_HIER.u_pwrmgr_aon
`define ROM_CTRL_HIER       `TOP_HIER.u_rom_ctrl
`define RSTMGR_HIER         `TOP_HIER.u_rstmgr_aon
`define RV_DM_HIER          `TOP_HIER.u_rv_dm
`define RV_TIMER_HIER       `TOP_HIER.u_rv_timer
`define SENSOR_CTRL_HIER    `TOP_HIER.u_sensor_ctrl
`define SPI_DEVICE_HIER     `TOP_HIER.u_spi_device
`define SPI_HOST_HIER(i)    `TOP_HIER.u_spi_host``i
`define SRAM_CTRL_MAIN_HIER `TOP_HIER.u_sram_ctrl_main
`define SRAM_CTRL_RET_HIER  `TOP_HIER,u_sram_ctrl_ret_aon
`define SYSRST_CTRL_HIER    `TOP_HIER.u_sysrst_ctrl
`define UART_HIER(i)        `TOP_HIER.u_uart``i
`define USBDEV_HIER         `TOP_HIER.u_usbdev

  // Identifier for logs.
   string MsgId = $sformatf("%m");

  // Identifier for the envorinment to which this interface is passed on via uvm_config_db.
  string env_name = "env";

  // Directly connected to chip IOs.
  //
  // DO NOT manipulate this signal in test sequences directly. Use the individual functional
  // interfaces below instead.
  wire [IoNumTotal-1:0] ios;

  // Functional interface: for testing ALL chip IOs, such as pinmux and padctrl tests.
  pins_if#(.Width(IoNumTotal), .PullStrength("Weak")) ios_if(.pins(ios));

  // Weak pulls for each IO.
  //
  // All IOs are weak-pulled by default, using the ios_if interface. All IOs are pulled down, except
  // for the 4 below.
  initial begin
    // Enable weak pulldown on most signals.
    ios_if.pins_pd = '1;
    // These are "inactive high".
    ios_if.pins_pu[PorN] = 1;
    ios_if.pins_pu[UsbP] = 1;
    ios_if.pins_pu[IoR8] = 1;
    ios_if.pins_pu[IoR9] = 1;
    // Leave dedicated chip outputs undriven.
    ios_if.pins_pd[SpiHostCsL] = 0;
    ios_if.pins_pd[SpiHostClk] = 0;
  end

  // X-check monitor on chip IOs.
  //
  // Chip IOs must always either be undriven or driven to a known value. Xs indicate multiple
  // drivers, which is an issue likely caused by multiple functions simultaneously attempting to
  // control the shared (muxed) pads.
  initial begin
    wait (ios_if.pins_pd == {IoNumTotal{1'b1}});
    foreach (ios[i]) begin
      fork
        begin
          automatic int a_i = i;
          forever @(ios[a_i]) begin
            automatic chip_io_e io = chip_io_e'(a_i);
            `DV_CHECK_FATAL(ios[a_i] !== 1'bx,
                            $sformatf("Possible multiple drivers on chip IO %0s", io.name()), MsgId)
          end
        end
      join_none
    end
  end

  // Functional interfaces.
  //
  // The section below creates functional interfaces and connects the signals to the `ios` wires.
  // Depending on the type of the IO, the following signaling choices are made:
  //
  // -  For all dedicated and muxed IOs that are spare pins:
  //   - Create pins_if instance, since it internally has direction controls. If a dedicated IO has
  //   fixed direction, we still create a pins_if instance so that the default weak pulls
  //   implemented in ios_if work properly.
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
  // DO NOT USE logic datatype to drive the ios signals directly.
  //
  // On the muxed IOs, multiple functional interfaces are connected to the same `ios` wires. A
  // single `ios` wire cannot be driven by more than one function at the same time. This must be
  // handled properly by the test sequence, which will enable the direction control for the required
  // interfaces based on the test's needs at the right times. By default, all chip IOs are weak
  // pulled via the chip_ios_if direction controls. If multiple drivers are found, The unknown
  // monitor above will throw a fatal error and exit the simulation.

  // Functional (dedicated) interface (input): power on reset input.
  pins_if #(1) por_n_if(.pins(ios[PorN]));

  // Functional (dedicated) interface (inout): USB.
  // TODO!

  // Functional (dedicated) interface (input): CC1, CC2.
  pins_if #(2) cc_if(.pins(ios[CC2:CC1]));

  // Functional (dedicated) interface (analog input): flash test volt.
  pins_if #(1) flash_test_volt_if(.pins(ios[FlashTestVolt]));

  // Functional (dedicated) interface (input): flash test mode0.
  pins_if #(2) flash_test_mode_if(.pins(ios[FlashTestMode1:FlashTestMode0]));

  // Functional (dedicated) interface (analog input): OTP ext volt.
  pins_if #(1) otp_ext_volt_if(.pins(ios[OtpExtVolt]));

  // Functional (dedicated) interface: SPI host interface (drives traffic into the chip).
  // TODO: Update spi_if to emit all signals as inout ports.
  // spi_if spi_host_if(.rst_n(top_earlgrey.u_spi_device.rst_ni),
  //                    .sck(ios[SpiDevClk]),
  //                    .csb(ios[SpiDevCsL]),
  //                    .sio(ios[SpiDevD3:SpiDevD0]));

  spi_if spi_host_if(.rst_n(`SPI_DEVICE_HIER.rst_ni));
  assign ios[SpiDevClk] = spi_host_if.sck;
  assign ios[SpiDevCsL] = spi_host_if.csb;
  assign ios[SpiDevD0] = spi_host_if.sio[0];
  assign spi_host_if.sio[1] = ios[SpiDevD1];

  // Functional (dedicated) interface: SPI AP device interface (receives traffic from the chip).
  spi_if spi_device_ap_if(.rst_n(`SPI_HOST_HIER(0).rst_ni));
  assign spi_device_ap_if.sck = ios[SpiHostClk];
  assign spi_device_ap_if.csb = ios[SpiHostCsL];
  // for (genvar i = 0; i < 4; i++) begin : gen_spi_device_ap_if_sio_conn
  //   // TODO: This logic needs to be firmed up.
  //   assign ios[SpiHostD0 + i] = spi_device_ap_if.sio_oe[i] ? spi_device_ap_if.sio[i] : 1'bz;
  //   assign spi_device_ap_if.sio[i] = ~spi_device_ap_if.sio_oe[i] ? ios[SpiHostD0 + i] : 1'bz;
  // end

  // Functional (dedicated) interface (inout): EC reset.
  pins_if #(1) ec_rst_l_if(.pins(ios[IoR8]));

  // Functional (dedicated) interface (inout): flash write protect.
  pins_if #(1) flash_wp_l_if(.pins(ios[IoR9]));

  // Functional (dedicated) interface (inout): power button.
  pins_if #(1) pwrb_in_if(.pins(ios[IoR13]));  // TODO: move to R0.

  // Functional (muxed) interface: sysrst_ctrl.
  // TODO: Replace with sysrst_ctrl IP level interface.
  // TODO; combine all into 1 single sysrst_ctrl_if.
  pins_if #(8) sysrst_ctrl_if(.pins({ios[IoB3], ios[IoB6], ios[IoB8], ios[IoB9],
                                     ios[IoC7], ios[IoC9], ios[IoR5], ios[IoR6]}));

  // Functional (dedicated) interface (input): AST misc.
  pins_if #(1) ast_misc_if(.pins(ios[AstMisc]));

  // Functional (muxed) interface: GPIOs.
  //
  // Note: In an actual implementation, fewer GPIOs may be in use. For testing, we try to connect as
  // many as the `gpio` peripheral supports. As of now, the other functions muxed with these IOs
  // do not need to be enabled in GPIO tests.
  pins_if #(31) gpio_pins_if(
    .pins({ios[IoA0], ios[IoA1], ios[IoA2], ios[IoA3],
           ios[IoA4], ios[IoA5], ios[IoA6], ios[IoB0],
           ios[IoB1], ios[IoB2], ios[IoB3], ios[IoB4],
           ios[IoB5], ios[IoB6], ios[IoB7], ios[IoB8],
           ios[IoC5], ios[IoC6], ios[IoC7], ios[IoC9],
           ios[IoC10], ios[IoC11], ios[IoC12], ios[IoR0],
           ios[IoR1], ios[IoR2], ios[IoR3], ios[IoR4],
           ios[IoR5], ios[IoR6], ios[IoR7]})
  );

  // Functional (muxed) interface: JTAG (valid during debug enabled LC state only).
  wire lc_hw_debug_en = (`LC_CTRL_HIER.lc_hw_debug_en_o == lc_ctrl_pkg::On);
  bit enable_jtag, jtag_enabled;
  jtag_if jtag_if();

  assign jtag_enabled = enable_jtag && lc_hw_debug_en;
  assign ios[IoR0] = jtag_enabled ? jtag_if.tms : 1'bz;
  assign jtag_if.tdo = jtag_enabled ? ios[IoR1] : 1'bz;
  assign ios[IoR2] = jtag_enabled ? jtag_if.tdi : 1'bz;
  assign ios[IoR3] = jtag_enabled ? jtag_if.tck : 1'bz;
  assign ios[IoR4] = jtag_enabled ? jtag_if.trst_n : 1'bz;

  // Functional (muxed) interface: Flash controller JTAG.
  logic enable_flash_ctrl_jtag, flash_ctrl_jtag_enabled;
  jtag_if flash_ctrl_jtag_if();

  assign flash_ctrl_jtag_enabled = enable_flash_ctrl_jtag && lc_hw_debug_en;
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

  // Functional (muxed) interface: PAD2AST.
  pins_if #(8) pad2ast_if(.pins({ios[IoA4], ios[IoA5], ios[IoB0], ios[IoB1],
                                 ios[IoB2], ios[IoC1], ios[IoC2], ios[IoC3]}));

  // Functional (muxed) interface: Pin wake up signal.
  // TODO: For these tests, use chip_pins_if instead, so that any pin can be configured to wakeup.
  pins_if #(1) pinmux_wkup_if(.pins(ios[IoB7]));

  // Functional (muxed) interface: UARTs.
  localparam chip_io_e AssignedUartTxIos[NUM_UARTS] = {IoC4, IoB5, IoA5, IoA1};
  localparam chip_io_e AssignedUartRxIos[NUM_UARTS] = {IoC3, IoB4, IoA4, IoA0};
  bit [NUM_UARTS-1:0] __enable_uart;  // Internal signal.

  for (genvar i = 0; i < NUM_UARTS; i++) begin : gen_uart_if_conn
    uart_if uart_if();
    assign ios[AssignedUartRxIos[i]] = __enable_uart[i] ? uart_if.uart_rx : 1'bz;
    assign uart_if.uart_tx = __enable_uart[i] ? ios[AssignedUartTxIos[i]] : 1'b1;

    initial begin
      uvm_config_db#(virtual uart_if)::set(null, $sformatf("*.env.m_uart_agent%0d*", i),
                                           "vif", uart_if);
    end
  end : gen_uart_if_conn

  // Connects / disconnects the UART interfaces to / from the chip IOs.
  //
  // The pinmux must be programmed to connect the UART peripheral to the IO pins referenced above,
  // in addition to UART interface being connected to the chip IOs. There may be a delay between
  // these two events. When the test sequence enables UART on the chip IOs, we immediately flip
  // the default pull on the assigned chip IOs to weak pullup to ensure protocol compliance.
  function automatic void enable_uart(int inst_num, bit enable);
    `DV_CHECK_FATAL(inst_num inside {[0:NUM_UARTS-1]}, , MsgId)
    ios_if.pins_pu[AssignedUartTxIos[inst_num]] = enable;
    ios_if.pins_pu[AssignedUartRxIos[inst_num]] = enable;
    __enable_uart[inst_num] = enable;
  endfunction

  // Functional (muxed) interface: SPI EC device interface (receives traffic from the chip).
  // spi_if spi_device_ec_if(.rst_n(top_earlgrey.u_spi_host1.rst_ni));
  // assign spi_device_ec_if.csk = ios[IoB3];
  // assign spi_device_ec_if.csb = ios[IoB0];
  // assign spi_device_ec_if.sio[0] = ios[IoB1];
  // assign ios[IoB2] = assign spi_device_ec_if.sio[1] : 1'bz;

  // Functional (muxed) interface: I2Cs.
  bit [NUM_I2CS-1:0] enable_i2c;
  // TODO: Update i2c_if to emit all signals as inout ports.
  // TODO: i2c_if i2c_if[NUM_I2CS-1:0]();

  // Functional (muxed) interface: PWM.
  localparam chip_io_e AssignedPwmIos[NUM_PWM_CHANNELS] = {IoB10, IoB11, IoB12,
                                                           IoC10, IoC11, IoC12};

  for (genvar i = 0; i < NUM_PWM_CHANNELS; i++) begin : gen_pwm_if_conn
    pwm_if pwm_if(.clk(`PWM_HIER.clk_i), .rst_n(`PWM_HIER.rst_ni));
    assign pwm_if.pwm = ios[AssignedPwmIos[i]];

    initial begin
      uvm_config_db#(virtual pwm_if)::set(null, $sformatf("*.env.m_pwm_monitor%0d*", i),
                                          $sformatf("m_pwm_monitor%0d_vif", i), pwm_if);
    end
  end : gen_pwm_if_conn

  // Functional (muxed) interface: external clock source.
  //
  // The reset port is passive only.
  clk_rst_if#("ExtClkDriver") ext_clk_if(.clk(ios[IoC6]), .rst_n(ios[PorN]));

  // Internal probes / monitors.

  // Legacy clk_rst_if mainly used passively for waiting for clock and reset events.
  clk_rst_if clk_rst_if(.clk(ios[IoC6]), .rst_n(ios[PorN]));

  wire cpu_clk = `CPU_HIER.clk_i;
  wire cpu_rst_n = `CPU_HIER.rst_ni;
  clk_rst_if cpu_clk_rst_if(.clk(cpu_clk), .rst_n(cpu_rst_n));

  wire aon_clk = `CLKMGR_HIER.clocks_o.clk_aon_powerup;
  wire aon_rst_n = `RSTMGR_HIER.resets_o.rst_por_aon_n[0];
  clk_rst_if aon_clk_rst_if(.clk(aon_clk), .rst_n(aon_rst_n));

  wire usb_clk = `USBDEV_HIER.clk_i;
  wire usb_rst_n = `USBDEV_HIER.rst_ni;
  clk_rst_if usb_clk_rst_if(.clk(usb_clk), .rst_n(usb_rst_n));

  wire pwrmgr_low_power = `PWRMGR_HIER.low_power_o;

  // alert_esc_if alert_if[NUM_ALERTS](.clk  (`ALERT_HANDLER_HIER.clk_i),
  //                                   .rst_n(`ALERT_HANDLER_HIER.rst_ni));
  // for (genvar i = 0; i < NUM_ALERTS; i++) begin : gen_alert_rx_conn
  //   assign alert_if[i].alert_rx = `ALERT_HANDLER_HIER.alert_rx_o[i];
  // end

  alerts_if alerts_if(.clk(`ALERT_HANDLER_HIER.clk_i), .rst_ni(`ALERT_HANDLER_HIER.rst_ni),
                      .alerts(`ALERT_HANDLER_HIER.alert_trig));

  // TODO: use pwrmgr_low_power, internal aon clk / rst monitor instead.
  pwrmgr_low_power_if pwrmgr_low_power_if(.clk     (`CLKMGR_HIER.clocks_o.clk_aon_powerup),
                                          .fast_clk(`CLKMGR_HIER.clocks_o.clk_io_div4_powerup),
                                          .rst_n   (`RSTMGR_HIER.resets_o.rst_por_io_div4_n[0]));
  assign pwrmgr_low_power_if.low_power = `PWRMGR_HIER.low_power_o;

  // Use this until we decide what to do with m_tl_agent_rv_dm_debug_mem_reg_block
  // TODO reveiw m_tl_agent_rv_dm_debug_mem_reg_block.
  tl_if dmi_tbd_if(.clk(cpu_clk), .rst_n(cpu_rst_n));

  // Stub CPU envorinment.
  //
  // The initial value is sought from a plusarg. It can however, be set by the sequence on the fly
  // as well. If enabled, the following things happen:
  // 1. The clock to the CPU is forced off.
  // 2. The address translation modules in rv_core_ibex are held in reset.
  // 3. The TL agent interface takes over the tl_d interface on the adapter.
  bit stub_cpu;
  tl_if cpu_d_tl_if(.clk(cpu_clk), .rst_n(cpu_rst_n));

  initial begin
    void'($value$plusargs("stub_cpu=%0b", stub_cpu));
    forever begin
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
        force `CPU_TL_ADAPT_D_HIER.tl_out = cpu_d_tl_if.h2d;
        force cpu_d_tl_if.d2h = `CPU_TL_ADAPT_D_HIER.tl_i;

        // TL command integrity gen is in the design data path. TL driver provides correct cmd intg.
        // Here forces it to random value to ensure that design generates the cmd intg
        fork
          forever begin : stub_cpu_cmd_intg_thread
            @(cpu_d_tl_if.h2d.a_valid);
            if (cpu_d_tl_if.h2d.a_valid) begin
              force `CPU_TL_ADAPT_D_HIER.tl_out.a_user.cmd_intg = $urandom;
            end else begin
              release `CPU_TL_ADAPT_D_HIER.tl_out.a_user.cmd_intg;
            end
          end
        join_none

        // In stub_cpu mode, disable these assertions because writing rand value to clkmgr's CSR
        // `extclk_sel` can violate these assertions.
        $assertoff(0, u_ast.u_ast_clks_byp.u_all_clk_byp_req.PrimMubi4SyncCheckTransients_A);
        $assertoff(0, u_ast.u_ast_clks_byp.u_all_clk_byp_req.PrimMubi4SyncCheckTransients0_A);
        $assertoff(0, u_ast.u_ast_clks_byp.u_all_clk_byp_req.PrimMubi4SyncCheckTransients1_A);
      end else begin
        // when en_sim_sram == 1, need to make sure the access to sim_sram doesn't appear on
        // cpu_d_tl_if, otherwise, we may have unmapped access as scb doesn't regnize addresses of
        // sim_sram. `CPU_HIER.tl_d_* is the right place to avoid seeing sim_sram accesses
        force cpu_d_tl_if.h2d = `CPU_HIER.cored_tl_h_o;
        force cpu_d_tl_if.d2h = `CPU_HIER.cored_tl_h_i;
      end
      @stub_cpu;
      disable stub_cpu_cmd_intg_thread;
    end
  end

  // Pass interface handles to uvm_config_db.
  //
  // Since the chip_if handle itself will be passed to the chip env, there is no need to set
  // sub-interface handles that are consumed by the chip env. Only pass the sub-interface handles
  // for external interface agents.
  initial begin
    // TODO: Should we always drive external clock? This should move to the sequences.
    ext_clk_if.set_active(.drive_clk_val(1), .drive_rst_n_val(0));

    // Note that attempting to drive the external clock / power on reset using this interface will
    // vacuously return instead of throwing an error. This is done to support the our base classes.
    // The test sequences must use ext_clk_if and por_n_if respectively instead.
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", clk_rst_if);

    // TODO: Update once jtag_riscv_agent is replaced with jtag_dmi_agent / SBA accessor.
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_riscv_agent*", "vif", jtag_if);

    uvm_config_db#(virtual tl_if)::set(
        null, "*.env.m_tl_agent_chip_reg_block*", "vif", cpu_d_tl_if);

    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_host_if);

    uvm_config_db#(virtual clk_rst_if)::set(
        null, "*.env", "clk_rst_vif_rv_dm_debug_mem_reg_block", cpu_clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_rv_dm*", "vif", dmi_tbd_if);

    // foreach (alert_if[i]) begin
    //   uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.m_alert_agent_%0s",
    //       LIST_OF_ALERTS[i]), "vif", alert_if[i]);
    // end
  end

  // Helper methods.
  function automatic string get_hier_path(chip_peripheral_e peripheral, int inst_num = 0);
    string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
    case (peripheral)
      AdcCtrl:      path = {path, ".", `DV_STRINGIFY(`ADC_CTRL_HIER)};
      Aes:          path = {path, ".", `DV_STRINGIFY(`AES_HIER)};
      AlertHandler: path = {path, ".", `DV_STRINGIFY(`ALERT_HANDLER_HIER)};
      AonTimer:     path = {path, ".", `DV_STRINGIFY(`AON_TIMER_HIER)};
      Ast:          path = {path, ".", `DV_STRINGIFY(`AST_HIER)};
      Clkmgr:       path = {path, ".", `DV_STRINGIFY(`CLKMGR_HIER)};
      Csrng:        path = {path, ".", `DV_STRINGIFY(`CSRNG_HIER)};
      Edn:          path = {path, ".", `DV_STRINGIFY(`EDN_HIER()), $sformatf(inst_num)};
      EntropySrc:   path = {path, ".", `DV_STRINGIFY(`ENTROPY_SRC_HIER)};
      FlashCtrl:    path = {path, ".", `DV_STRINGIFY(`FLASH_CTRL_HIER)};
      Gpio:         path = {path, ".", `DV_STRINGIFY(`GPIO_HIER)};
      Hmac:         path = {path, ".", `DV_STRINGIFY(`HMAC_HIER)};
      I2c:          path = {path, ".", `DV_STRINGIFY(`I2C_HIER()), $sformatf(inst_num)};
      Keymgr:       path = {path, ".", `DV_STRINGIFY(`KEYMGR_HIER)};
      Kmac:         path = {path, ".", `DV_STRINGIFY(`KMAC_HIER)};
      LcCtrl:       path = {path, ".", `DV_STRINGIFY(`LC_CTRL_HIER)};
      Otbn:         path = {path, ".", `DV_STRINGIFY(`OTBN_HIER)};
      OtpCtrl:      path = {path, ".", `DV_STRINGIFY(`OTP_CTRL_HIER)};
      SramCtrlMain: path = {path, ".", `DV_STRINGIFY(`SRAM_CTRL_MAIN_HIER)};
      SramCtrlRet:  path = {path, ".", `DV_STRINGIFY(`SRAM_CTRL_RET_HIER)};
      Pattgen:      path = {path, ".", `DV_STRINGIFY(`PATTGEN_HIER)};
      Pinmux:       path = {path, ".", `DV_STRINGIFY(`PINMUX_HIER)};
      Pwrmgr:       path = {path, ".", `DV_STRINGIFY(`PWRMGR_HIER)};
      Pwm:          path = {path, ".", `DV_STRINGIFY(`PWM_HIER)};
      RomCrl:       path = {path, ".", `DV_STRINGIFY(`ROM_CTRL_HIER)};
      RstMgr:       path = {path, ".", `DV_STRINGIFY(`RSTMGR_HIER)};
      RvDm:         path = {path, ".", `DV_STRINGIFY(`RV_DM_HIER)};
      RvTimer:      path = {path, ".", `DV_STRINGIFY(`RV_TIMER_HIER)};
      SpiDevice:    path = {path, ".", `DV_STRINGIFY(`SPI_DEVICE_HIER)};
      SpiHost:      path = {path, ".", `DV_STRINGIFY(`SPI_HOST_HIER()), $sformatf(inst_num)};
      SysRstCtrl:   path = {path, ".", `DV_STRINGIFY(`SYSRST_CTRL_HIER)};
      Uart:         path = {path, ".", `DV_STRINGIFY(`UART_HIER()), $sformatf(inst_num)};
      UsbDev:       path = {path, ".", `DV_STRINGIFY(`USBDEV_HIER)};
      default:      `uvm_fatal(MsgId, $sformatf("Bad peripheral: %0s", peripheral.name()))
    endcase
    return path;
  endfunction

`undef TOP_HIER
`undef ADC_CTRL_HIER
`undef AES_HIER
`undef ALERT_HANDLER_HIER
`undef AON_TIMER_HIER
`undef AST_HIER
`undef CLKMGR_HIER
`undef CPU_HIER
`undef CPU_CORE_HIER
`undef CPU_TL_ADAPT_D_HIER
`undef CSRNG_HIER
`undef ENTROPY_SRC_HIER
`undef EDN_HIER
`undef FLASH_CTRL_HIER
`undef GPIO_HIER
`undef HMAC_HIER
`undef I2C_HIER
`undef KMAC_HIER
`undef KEYMGR_HIER
`undef LC_CTRL_HIER
`undef OTP_CTRL_HIER
`undef OTBN_HIER
`undef PATTGEN_HIER
`undef PINMUX_HIER
`undef PWM_HIER
`undef PWRMGR_HIER
`undef ROM_CTRL_HIER
`undef RSTMGR_HIER
`undef RV_DM_HIER
`undef RV_TIMER_HIER
`undef SENSOR_CTRL_HIER
`undef SPI_DEVICE_HIER
`undef SPI_HOST_HIER
`undef SRAM_CTRL_MAIN_HIER
`undef SRAM_CTRL_RET_HIER
`undef SYSRST_CTRL_HIER
`undef UART_HIER
`undef USBDEV_HIER

endinterface
