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
  import top_earlgrey_pkg::*;
  import dv_utils_pkg::*;
  import uvm_pkg::*;

  `include "dv_macros.svh"
  `include "uvm_macros.svh"

  // TODO: Move these to `include "./chip_hier_macros.svh". Deprecate ../tb/chip_hier_macros.svh.
  // TODO: In Xcelium, the bind is not exposing the internal hierarchies to chip_if.
  // TODO: Autogen this in top_<top>_pkg.
`ifdef XCELIUM
  `define TOP_HIER          tb.dut.top_earlgrey
`else
  `define TOP_HIER          top_earlgrey
`endif
`define ADC_CTRL_HIER       `TOP_HIER.u_adc_ctrl_aon
`define AES_HIER            `TOP_HIER.u_aes
`define AES_CONTROL_HIER    `AES_HIER.u_aes_core.u_aes_control
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
`define IBEX_HIER           `CPU_CORE_HIER.u_ibex_core
`define IBEX_CSRS_HIER      `IBEX_HIER.cs_registers_i
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
`define RV_CORE_IBEX_HIER   `TOP_HIER.u_rv_core_ibex
`define RV_DM_HIER          `TOP_HIER.u_rv_dm
`define RV_PLIC_HIER        `TOP_HIER.u_rv_plic
`define RV_TIMER_HIER       `TOP_HIER.u_rv_timer
`define SENSOR_CTRL_HIER    `TOP_HIER.u_sensor_ctrl_aon
`define SPI_DEVICE_HIER     `TOP_HIER.u_spi_device
`define SPI_HOST_HIER(i)    `TOP_HIER.u_spi_host``i
`define SRAM_CTRL_MAIN_HIER `TOP_HIER.u_sram_ctrl_main
`define SRAM_CTRL_RET_HIER  `TOP_HIER.u_sram_ctrl_ret_aon
`define SYSRST_CTRL_HIER    `TOP_HIER.u_sysrst_ctrl_aon
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
  wire [top_earlgrey_pkg::DioPadCount-1:0] dios;
  wire [top_earlgrey_pkg::MioPadCount-1:0] mios;

  // Functional interface: for testing ALL chip IOs, such as pinmux and padctrl tests.
  pins_if#(.Width(top_earlgrey_pkg::MioPadCount), .PullStrength("Weak")) mios_if(.pins(mios));
  pins_if#(.Width(top_earlgrey_pkg::DioPadCount), .PullStrength("Weak")) dios_if(.pins(dios));

  // Functional (dedicated) interface (input): AST misc.
  wire ast_misc;
  pins_if #(.Width(1), .PullStrength("Weak")) ast_misc_if(.pins(ast_misc));

  // Weak pulls for DIOs.
  //
  // These weak pulls enable all DIOs to reflect a legal value. Active low signals are pulled up,
  // the rest are pulled down.

  // The reason for having these is because the agent interface may be connected but may not be
  // "active", i.e. know what to drive. Secondly, the agent interfaces may be disconnected in favor
  // of using the "bit-bang" interface dios_if for tests such as pin wake up and pad attributes. If
  // weak pulls serve as a fall back when dios_if is connected, but it is not actively driving the
  // chip IOs. These situations result in X-prop / SVA errors thrown by the design.
  //
  // TODO: Fix the design / SVAs or the interface agents so that no default pulls are needed at all.
  function automatic void cfg_default_weak_pulls_on_dios(bit enable);
    if (enable) begin
      // Enable weak pull downs on DIOs.
      dios_if.pins_pd = '1;

      // These are active low, so pull up.
      dios_if.pins_pu[top_earlgrey_pkg::DioPadPorN] = 1;
      dios_if.pins_pu[top_earlgrey_pkg::DioPadUsbP] = 1;
      dios_if.pins_pu[top_earlgrey_pkg::DioPadIor8] = 1;
      dios_if.pins_pu[top_earlgrey_pkg::DioPadIor9] = 1;

      // No need of pulls for the SPI host peripheral.
      dios_if.pins_pd[top_earlgrey_pkg::DioPadSpiHostCsL:top_earlgrey_pkg::DioPadSpiHostD0] = '0;
    end else begin
      dios_if.disconnect();
    end
  endfunction

  initial begin
    cfg_default_weak_pulls_on_dios(1);
  end

  // X-check monitor on the muxed chip IOs.
  //
  // Chip IOs must always either be undriven or driven to a known value. Xs indicate multiple
  // drivers, which is an issue likely caused by multiple functions simultaneously attempting to
  // control the shared (muxed) pads.
  bit disable_mios_x_check = 0;
  for (genvar i = top_earlgrey_pkg::MioPadIoa0; i < top_earlgrey_pkg::MioPadCount; i++)
  begin : gen_mios_x_check
    wire glitch_free_io;
    assign #1ps glitch_free_io = mios[i];

    top_earlgrey_pkg::mio_pad_e named_io = top_earlgrey_pkg::mio_pad_e'(i);
    always (* xprop_off *) @(glitch_free_io) begin
      if (glitch_free_io === 1'bx && disable_mios_x_check == 0) begin
        `uvm_error(MsgId, $sformatf("Detected an X on %0s", named_io.name()))
      end
    end
  end : gen_mios_x_check

  // Functional interfaces.
  //
  // The section below creates functional interfaces and connects the signals to the `d|mios` wires.
  // Depending on the type of the IO, the following signaling choices are made:
  //
  // -  For all dedicated and muxed IOs that are spare pins:
  //   - Create pins_if instance, since it internally has direction controls. If a dedicated IO has
  //   fixed direction, we still create a pins_if instance so that the default weak pulls
  //   implemented in d|mios_if work properly.
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
  // DO NOT USE logic datatype to drive the d|mios signals directly.
  //
  // On the muxed IOs, multiple functional interfaces are connected to the same `mios` wires. A
  // single `mios` wire cannot be driven by more than one function at the same time. This must be
  // properly by the test sequence, which will enable the direction control for the required
  // interfaces based on the test's needs at the right times. If multiple drivers are found, the
  // unknown monitor above will throw a fatal error and exit the simulation.

  // Functional (dedicated) interface (input): power on reset input.
  pins_if #(.Width(1), .PullStrength("Weak")) por_n_if(.pins(dios[top_earlgrey_pkg::DioPadPorN]));

  // Functional (dedicated) interface (inout): USB.
  // TODO!

  // Functional (dedicated) interface (input): CC1, CC2.
  pins_if #(.Width(2), .PullStrength("Weak")) cc_if(
    .pins(dios[top_earlgrey_pkg::DioPadCc2:top_earlgrey_pkg::DioPadCc1])
  );

  // Functional (dedicated) interface (analog input): flash test volt.
  pins_if #(.Width(1), .PullStrength("Weak")) flash_test_volt_if(
    .pins(dios[top_earlgrey_pkg::DioPadFlashTestVolt])
  );

  // Functional (dedicated) interface (input): flash test mode0.
  pins_if #(.Width(2), .PullStrength("Weak")) flash_test_mode_if(
    .pins(dios[top_earlgrey_pkg::DioPadFlashTestMode1:top_earlgrey_pkg::DioPadFlashTestMode0])
  );

  // Functional (dedicated) interface (analog input): OTP ext volt.
  pins_if #(.Width(1), .PullStrength("Weak")) otp_ext_volt_if(
    .pins(dios[top_earlgrey_pkg::DioPadOtpExtVolt])
  );

  // Functional (dedicated) interface: SPI host interface (drives traffic into the chip).
  bit enable_spi_host = 1;
  bit enable_spi_tpm;
  spi_if spi_host_if(
    .rst_n(`SPI_DEVICE_HIER.rst_ni),
    .sio  (dios[top_earlgrey_pkg::DioPadSpiDevD3:top_earlgrey_pkg::DioPadSpiDevD0])
  );
  assign dios[top_earlgrey_pkg::DioPadSpiDevClk] = enable_spi_host | enable_spi_tpm ?
      spi_host_if.sck : 1'bz;
  assign dios[top_earlgrey_pkg::DioPadSpiDevCsL] = enable_spi_host ? spi_host_if.csb[0] : 1'bz;
  assign mios[top_earlgrey_pkg::MioPadIoa7] = enable_spi_tpm ? spi_host_if.csb[1] : 1'bz;
  initial begin
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_host_agent*", "vif", spi_host_if);
    do begin
      spi_host_if.disconnect(!enable_spi_host & !enable_spi_tpm);
      @(enable_spi_host | enable_spi_tpm);
    end while (1);
  end

  // Functional (dedicated) interface: SPI device 0 interface (receives traffic from the chip).
  // TODO: Update spi_if to emit all signals as inout ports and internal drivers on all ports.
  bit [NUM_SPI_HOSTS-1:0] __enable_spi_device;

  spi_if spi_device0_if(
    .rst_n(`SPI_HOST_HIER(0).rst_ni),
    .sio  (dios[top_earlgrey_pkg::DioPadSpiHostD3:
                top_earlgrey_pkg::DioPadSpiHostD0])
  );

  assign spi_device0_if.sck = __enable_spi_device[0] ?
      dios[top_earlgrey_pkg::DioPadSpiHostClk] : 1'bz;

  assign spi_device0_if.csb = __enable_spi_device[0] ?
      {'1, dios[top_earlgrey_pkg::DioPadSpiHostCsL]} : '1;

  initial begin
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_device_agents0*", "vif", spi_device0_if);
    do begin
      spi_device0_if.disconnect(!__enable_spi_device[0]);
      @(__enable_spi_device[0]);
    end while(1);
  end

  // Functional (muxed) interface: SPI device 1 interface (receives traffic from the chip).
  spi_if spi_device1_if(
    .rst_n(`SPI_HOST_HIER(1).rst_ni),
    .sio  ({mios[top_earlgrey_pkg::MioPadIob6],  // sio[3]
            mios[top_earlgrey_pkg::MioPadIob5],  // sio[2]
            mios[top_earlgrey_pkg::MioPadIob4],  // sio[1]
            mios[top_earlgrey_pkg::MioPadIob3]}) // sio[0]
  );

  assign spi_device1_if.sck = __enable_spi_device[1] ?
      mios[top_earlgrey_pkg::MioPadIob0] : 1'bz;

  assign spi_device1_if.csb = __enable_spi_device[1] ?
      {'1, mios[top_earlgrey_pkg::MioPadIob1]} : '1;

  initial begin
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_device_agents1*", "vif", spi_device1_if);
    do begin
      spi_device1_if.disconnect(!__enable_spi_device[1]);
      @(__enable_spi_device[1]);
    end while(1);
  end

  // Enables tb spi_device, which connects to dut spi_host
  function automatic void enable_spi_device(int inst_num, bit enable);
    `DV_CHECK_FATAL(inst_num inside {[0:NUM_SPI_HOSTS-1]}, , MsgId)
    `uvm_info(MsgId, $sformatf("enable spi device %0d", inst_num), UVM_LOW)
    __enable_spi_device[inst_num] = enable;
  endfunction : enable_spi_device


  // Functional (dedicated) interface (inout): EC reset.
  pins_if #(.Width(1), .PullStrength("Weak")) ec_rst_l_if(
    .pins(dios[top_earlgrey_pkg::DioPadIor8])
  );

  // Functional (dedicated) interface (inout): flash write protect.
  pins_if #(.Width(1), .PullStrength("Weak")) flash_wp_l_if(
    .pins(dios[top_earlgrey_pkg::DioPadIor9])
  );

  // Functional (dedicated) interface (inout): power button.
  pins_if #(.Width(1), .PullStrength("Weak")) pwrb_in_if(
    .pins(mios[top_earlgrey_pkg::MioPadIor13])
  );  // TODO: move to R0.

  // Functional (muxed) interface: sysrst_ctrl.
  // TODO: Replace with sysrst_ctrl IP level interface.
  // TODO; combine all into 1 single sysrst_ctrl_if.
  pins_if #(.Width(8), .PullStrength("Weak")) sysrst_ctrl_if(
    .pins({mios[top_earlgrey_pkg::MioPadIor6], mios[top_earlgrey_pkg::MioPadIor5],
           mios[top_earlgrey_pkg::MioPadIoc9], mios[top_earlgrey_pkg::MioPadIoc7],
           mios[top_earlgrey_pkg::MioPadIob9], mios[top_earlgrey_pkg::MioPadIob8],
           mios[top_earlgrey_pkg::MioPadIob6], mios[top_earlgrey_pkg::MioPadIob3]})
  );

  // Functional (muxed) interface: DFT straps.
  pins_if #(.Width(2), .PullStrength("Weak")) dft_straps_if(
    .pins(mios[top_earlgrey_pkg::MioPadIoc4:top_earlgrey_pkg::MioPadIoc3])
  );

  // Functional (muxed) interface: TAP straps.
  pins_if #(.Width(2), .PullStrength("Weak")) tap_straps_if(
    .pins({mios[top_earlgrey_pkg::MioPadIoc5], mios[top_earlgrey_pkg::MioPadIoc8]})
  );

  // Weakly pulldown TAP & DFT strap pins in DFT-enabled LC states.
  //
  // The TAP strap sampling logic continuously samples the strap values in DFT-enabled LC
  // state to allow fast-switching back and forth between LC and RV_DM TAPs. The TAP strap pins are
  // muxed IOs which are unconnected to any interface by default, leaving them in an undriven state.
  // The test may put the chip in such an LC state for various reasons. Such tests may not even
  // set the TAP strap pins or exercise the JTAG interface. The side-effect of this is, when the
  // continuous strap sampling logic samples an undriven value, it results in X-propagation. To
  // avoid that, it is necessary to weakly pull down the strap pins. The DFT strap pins have a
  // same issue, except that it is sampled only once during power up.
  //
  // The pinmux version of lc_dft_en is used below because it goes through synchronizers.
`ifdef GATE_LEVEL
  wire pinmux_lc_dft_en =
  (`PINMUX_HIER.u_pinmux_strap_sampling.u_prim_lc_sync_lc_dft_en.lc_en_o[3:0] == lc_ctrl_pkg::On);
`else
  wire pinmux_lc_dft_en = (`PINMUX_HIER.u_pinmux_strap_sampling.lc_dft_en[0] == lc_ctrl_pkg::On);
`endif
  wire pinmux_lc_hw_debug_en = `PINMUX_HIER.u_pinmux_strap_sampling.pinmux_hw_debug_en_o ==
                               lc_ctrl_pkg::On;

`ifdef GATE_LEVEL
  wire pwrmgr_fast_pwr_state_strap_en = `PINMUX_HIER.u_pinmux_strap_sampling.strap_en_q_reg.Q;
`else
  wire pwrmgr_fast_pwr_state_strap_en = `PINMUX_HIER.u_pinmux_strap_sampling.strap_en_q;
`endif
  initial begin
    fork
      forever @(pwrmgr_fast_pwr_state_strap_en or pinmux_lc_dft_en) begin
        // TAP straps are continuously sampled in active power.
        if (pinmux_lc_dft_en || pwrmgr_fast_pwr_state_strap_en) begin
          tap_straps_if.pins_pd = '1;
        end else begin
          tap_straps_if.pins_pd = '0;
        end
        // DFT straps are sampled only once, during a specific pwrmgr FSM state.
        if (pinmux_lc_dft_en && pwrmgr_fast_pwr_state_strap_en) begin
          dft_straps_if.pins_pd = '1;
        end else begin
          dft_straps_if.pins_pd = '0;
        end
      end
    join_none
  end

  // Set JTAG TAP straps during the next powerup.
  //
  // The function waits for the pwrmgr fast FSM state to reach the strap sampling state and sets the
  // JTAG TAP strap pins to the desired values. This function must be called after asserting POR
  // or just before a new low power entry. The strap pins are set the moment pwrmgr FSM reaches the
  // strap sampling state. The strap interface is disconnected from the chip IOs immediately once
  // the pwrmgr advances to the next state, so that the chip IOs are freed up for other uses.
  //
  // In DFT-enabled LC state, the TAP straps are continuously sampled to allow switching back and
  // forth between RV_DM and LC TAPs. For this usecase, the test sequence can set the TAP straps
  // directly using the tap_straps_if interface.
  //
  // This method is non-blocking - it immediately returns back to the caller after spawning a
  // thread. Care must be taken to ensure the calling thread is not killed unless desired.
  function automatic void set_tap_straps_on_powerup(chip_jtag_tap_e tap_strap);
    fork begin
      wait (pwrmgr_fast_pwr_state_strap_en);
      tap_straps_if.drive(tap_strap);
      wait (!pwrmgr_fast_pwr_state_strap_en);
      tap_straps_if.drive_en('0);
    end join_none
  endfunction

  // Set DFT straps during the next powerup.
  //
  // Similar in behavior to set_tap_straps_on_next_powerup(), but used for setting the DFT straps.
  function automatic void set_dft_straps_on_powerup(bit [1:0] dft_strap);
    fork begin
      wait (pwrmgr_fast_pwr_state_strap_en);
      dft_straps_if.drive(dft_strap);
      wait (!pwrmgr_fast_pwr_state_strap_en);
      dft_straps_if.drive_en('0);
    end join_none
  endfunction

  // Functional (muxed) interface: SW straps.
  pins_if #(.Width(3), .PullStrength("Weak")) sw_straps_if(
    .pins(mios[top_earlgrey_pkg::MioPadIoc2:top_earlgrey_pkg::MioPadIoc0])
  );

  // Functional (muxed) interface: GPIOs.
  //
  // The pins allocated for GPIOs overlap with several other functions, but that is ok. For pre-Si
  // DV, the directed tests that verify the GPIOs are not likely to also enable other functions that
  // overlap with these pins. If they do, we could set masks and limit the GPIOs to a smaller
  // subset. The selection below prevents as much contention as possible on the IOs, considering
  // various modes the testbench AND the device can be in.
  pins_if #(.Width(NUM_GPIOS), .PullStrength("Weak")) gpios_if(
    .pins({mios[top_earlgrey_pkg::MioPadIor13], mios[top_earlgrey_pkg::MioPadIor12],
           mios[top_earlgrey_pkg::MioPadIor11], mios[top_earlgrey_pkg::MioPadIor10],
           mios[top_earlgrey_pkg::MioPadIor7], mios[top_earlgrey_pkg::MioPadIor6],
           mios[top_earlgrey_pkg::MioPadIor5], mios[top_earlgrey_pkg::MioPadIor4],
           mios[top_earlgrey_pkg::MioPadIor3], mios[top_earlgrey_pkg::MioPadIor2],
           mios[top_earlgrey_pkg::MioPadIor1], mios[top_earlgrey_pkg::MioPadIor0],
           mios[top_earlgrey_pkg::MioPadIoc12], mios[top_earlgrey_pkg::MioPadIoc11],
           mios[top_earlgrey_pkg::MioPadIoc10], mios[top_earlgrey_pkg::MioPadIoc9],
           mios[top_earlgrey_pkg::MioPadIob12], mios[top_earlgrey_pkg::MioPadIob11],
           mios[top_earlgrey_pkg::MioPadIob10], mios[top_earlgrey_pkg::MioPadIob9],
           mios[top_earlgrey_pkg::MioPadIob8], mios[top_earlgrey_pkg::MioPadIob7],
           mios[top_earlgrey_pkg::MioPadIob6], mios[top_earlgrey_pkg::MioPadIoa8],
           mios[top_earlgrey_pkg::MioPadIoa7], mios[top_earlgrey_pkg::MioPadIoa6],
           mios[top_earlgrey_pkg::MioPadIoa5], mios[top_earlgrey_pkg::MioPadIoa4],
           mios[top_earlgrey_pkg::MioPadIoa3], mios[top_earlgrey_pkg::MioPadIoa2],
           mios[top_earlgrey_pkg::MioPadIoa1], mios[top_earlgrey_pkg::MioPadIoa0]})
  );

  // Functional (muxed) interface: JTAG (valid during debug enabled LC state only).

  // To connect the JTAG interface to chip IOs, just set the TAP strap to the desired value.
  //
  // Whether the desired JTAG TAP will actually selected or not depends on the LC state and the
  // window of time when the TAP straps are set. It is upto the test sequence to orchestrate it
  // correctly. Disconnect the TAP strap interface to free up the muxed IOs.
  wire __enable_jtag = |tap_straps_if.pins_oe;
  jtag_if jtag_if();

  assign mios[top_earlgrey_pkg::MioPadIor0] = __enable_jtag ? jtag_if.tms : 1'bz;
  assign jtag_if.tdo = __enable_jtag ? mios[top_earlgrey_pkg::MioPadIor1] : 1'bz;
  assign mios[top_earlgrey_pkg::MioPadIor2] = __enable_jtag ? jtag_if.tdi : 1'bz;
  assign mios[top_earlgrey_pkg::MioPadIor3] = __enable_jtag ? jtag_if.tck : 1'bz;
  assign mios[top_earlgrey_pkg::MioPadIor4] = __enable_jtag ? jtag_if.trst_n : 1'bz;

  function automatic void set_tdo_pull(bit value);
    if (value) begin
      mios_if.pins_pd[top_earlgrey_pkg::MioPadIor1] = 0;
      mios_if.pins_pu[top_earlgrey_pkg::MioPadIor1] = 1;
    end else begin
      mios_if.pins_pu[top_earlgrey_pkg::MioPadIor1] = 0;
      mios_if.pins_pd[top_earlgrey_pkg::MioPadIor1] = 1;
    end
  endfunction

  // Functional (muxed) interface: Flash controller JTAG.
  bit enable_flash_ctrl_jtag, flash_ctrl_jtag_enabled;
  jtag_if flash_ctrl_jtag_if();

  // TODO: Revisit this logic.
  wire lc_hw_debug_en = (`LC_CTRL_HIER.lc_hw_debug_en_o == lc_ctrl_pkg::On);
  assign flash_ctrl_jtag_enabled = enable_flash_ctrl_jtag && lc_hw_debug_en;
  assign mios[top_earlgrey_pkg::MioPadIob0] = flash_ctrl_jtag_enabled ?
      flash_ctrl_jtag_if.tms : 1'bz;
  assign flash_ctrl_jtag_if.tdo = flash_ctrl_jtag_enabled ?
      mios[top_earlgrey_pkg::MioPadIob1] : 1'bz;
  assign mios[top_earlgrey_pkg::MioPadIob2] = flash_ctrl_jtag_enabled ?
      flash_ctrl_jtag_if.tdi : 1'bz;
  assign mios[top_earlgrey_pkg::MioPadIob3] = flash_ctrl_jtag_enabled ?
      flash_ctrl_jtag_if.tck : 1'bz;

  // Functional (muxed) interface: AST2PAD.
  pins_if #(.Width(9), .PullStrength("Weak")) ast2pad_if(
    .pins({mios[top_earlgrey_pkg::MioPadIoa0], mios[top_earlgrey_pkg::MioPadIoa1],
           mios[top_earlgrey_pkg::MioPadIob3], mios[top_earlgrey_pkg::MioPadIob4],
           mios[top_earlgrey_pkg::MioPadIob5], mios[top_earlgrey_pkg::MioPadIoc0],
           mios[top_earlgrey_pkg::MioPadIoc4], mios[top_earlgrey_pkg::MioPadIoc7],
           mios[top_earlgrey_pkg::MioPadIoc9]})
  );

  // Functional (muxed) interface: PAD2AST.
  pins_if #(.Width(8), .PullStrength("Weak")) pad2ast_if(
    .pins({mios[top_earlgrey_pkg::MioPadIoa4], mios[top_earlgrey_pkg::MioPadIoa5],
           mios[top_earlgrey_pkg::MioPadIob0], mios[top_earlgrey_pkg::MioPadIob1],
           mios[top_earlgrey_pkg::MioPadIob2], mios[top_earlgrey_pkg::MioPadIoc1],
           mios[top_earlgrey_pkg::MioPadIoc2], mios[top_earlgrey_pkg::MioPadIoc3]})
  );

  // Functional (muxed) interface: Pin wake up signal.
  // TODO: For these tests, use chip_pins_if instead, so that any pin can be configured to wakeup.
  pins_if #(.Width(1), .PullStrength("Weak")) pinmux_wkup_if(
    .pins(mios[top_earlgrey_pkg::MioPadIob7])
  );

  // Functional (muxed) interface: UARTs.
  localparam int AssignedUartTxIos[NUM_UARTS] = {
      top_earlgrey_pkg::MioPadIoc4, top_earlgrey_pkg::MioPadIob5,
      top_earlgrey_pkg::MioPadIoa5, top_earlgrey_pkg::MioPadIoa1
  };
  localparam int AssignedUartRxIos[NUM_UARTS] = {
      top_earlgrey_pkg::MioPadIoc3, top_earlgrey_pkg::MioPadIob4,
      top_earlgrey_pkg::MioPadIoa4, top_earlgrey_pkg::MioPadIoa0
  };
  bit [NUM_UARTS-1:0] __enable_uart;  // Internal signal.

  for (genvar i = 0; i < NUM_UARTS; i++) begin : gen_uart_if_conn
    uart_if uart_if();
    assign mios[AssignedUartRxIos[i]] = __enable_uart[i] ? uart_if.uart_rx : 1'bz;
    assign uart_if.uart_tx = __enable_uart[i] ? mios[AssignedUartTxIos[i]] : 1'b1;

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
    mios_if.pins_pu[AssignedUartTxIos[inst_num]] = enable;
    mios_if.pins_pu[AssignedUartRxIos[inst_num]] = enable;
    __enable_uart[inst_num] = enable;
  endfunction


  // Functional (muxed) interface: I2Cs.
  bit [NUM_I2CS-1:0] __enable_i2c = {NUM_I2CS{1'b0}}; // Internal signal.

  // {ioa7, ioa8}, {iob9, iob10}, {iob11, iob12} are the i2c connections
  localparam int AssignedI2cSclIos [NUM_I2CS]  = {
    top_earlgrey_pkg::MioPadIoa8,
    top_earlgrey_pkg::MioPadIob9,
    top_earlgrey_pkg::MioPadIob11
  };
  localparam int AssignedI2cSdaIos [NUM_I2CS] = {
    top_earlgrey_pkg::MioPadIoa7,
    top_earlgrey_pkg::MioPadIob10,
    top_earlgrey_pkg::MioPadIob12
  };

  // This part unfortunately has to be hardcoded since the macro cannot interpret a genvar.
  wire [NUM_I2CS-1:0]i2c_clks = {`I2C_HIER(2).clk_i, `I2C_HIER(1).clk_i, `I2C_HIER(0).clk_i};
  wire [NUM_I2CS-1:0]i2c_rsts = {`I2C_HIER(2).rst_ni, `I2C_HIER(1).rst_ni, `I2C_HIER(0).rst_ni};

  for (genvar i = 0; i < NUM_I2CS; i++) begin : gen_i2c_if
    i2c_if i2c_if(
      .clk_i(i2c_clks[i]),
      .rst_ni(i2c_rsts[i]),
      .scl_io(mios[AssignedI2cSclIos[i]]),
      .sda_io(mios[AssignedI2cSdaIos[i]])
    );

    // connect to agents
    initial begin
      uvm_config_db#(virtual i2c_if)::set(null, $sformatf("*.env.m_i2c_agent%0d*", i),
      "vif", i2c_if);
    end
  end

  function automatic void enable_i2c(int inst_num, bit enable);
    `DV_CHECK_FATAL(inst_num inside {[0:NUM_I2CS-1]}, , MsgId)
    mios_if.pins_pu[AssignedI2cSclIos[inst_num]] = enable;
    mios_if.pins_pd[AssignedI2cSclIos[inst_num]] = 0;
    mios_if.pins_pu[AssignedI2cSdaIos[inst_num]] = enable;
    mios_if.pins_pd[AssignedI2cSdaIos[inst_num]] = 0;
    __enable_i2c[inst_num] = enable;
  endfunction

  // Functional (muxed) interface: PWM.
  localparam int AssignedPwmIos[NUM_PWM_CHANNELS] = {
      top_earlgrey_pkg::MioPadIob10, top_earlgrey_pkg::MioPadIob11, top_earlgrey_pkg::MioPadIob12,
      top_earlgrey_pkg::MioPadIoc10, top_earlgrey_pkg::MioPadIoc11, top_earlgrey_pkg::MioPadIoc12
  };

  for (genvar i = 0; i < NUM_PWM_CHANNELS; i++) begin : gen_pwm_if_conn
    pwm_if pwm_if(
`ifdef GATE_LEVEL
                  .clk (0),
                  .rst_n (1),
`else
                  .clk  (`CLKMGR_HIER.clocks_o.clk_aon_powerup),
                  .rst_n(`RSTMGR_HIER.resets_o.rst_lc_aon_n[0]),
`endif
                  .pwm  (mios[AssignedPwmIos[i]]));

    initial begin
      uvm_config_db#(virtual pwm_if)::set(null, $sformatf("*.env.m_pwm_monitor%0d*", i), "vif",
                                          pwm_if);
    end
  end : gen_pwm_if_conn

  // Functional (muxed) interface: PATTGEN
  // each channel has pda, pcl

  bit __enable_pattgen = 0;

  pattgen_if #(NUM_PATTGEN_CH) pattgen_if();
  assign pattgen_if.rst_ni = `PATTGEN_HIER.rst_ni;
  assign pattgen_if.clk_i  = `PATTGEN_HIER.clk_i;
  assign pattgen_if.pda_tx = !__enable_pattgen ? {NUM_PATTGEN_CH{1'bz}} :
                                                 {mios[top_earlgrey_pkg::MioPadIob11],
                                                  mios[top_earlgrey_pkg::MioPadIob9]};
  assign pattgen_if.pcl_tx = !__enable_pattgen ? {NUM_PATTGEN_CH{1'bz}} :
                                                 {mios[top_earlgrey_pkg::MioPadIob12],
                                                  mios[top_earlgrey_pkg::MioPadIob10]};

  initial begin
    uvm_config_db#(virtual pattgen_if)::set(null, "*.env.m_pattgen_agent*", "vif", pattgen_if);
  end
  function automatic void enable_pattgen(bit enable);
    __enable_pattgen = enable;
  endfunction

  // Functional (muxed) interface: external clock source.
  //
  // The reset port is passive only.
  clk_rst_if#("ExtClkDriver") ext_clk_if(
     .clk (mios[top_earlgrey_pkg::MioPadIoc6]),
    .rst_n(dios[top_earlgrey_pkg::DioPadPorN])
  );

  // Internal probes / monitors.
`ifdef GATE_LEVEL
  wire sys_clk = 1'b0;
  wire sys_rst_n = 1'b1;
`else
  wire sys_clk = `CLKMGR_HIER.clocks_o.clk_main_powerup;
  wire sys_rst_n = `RSTMGR_HIER.resets_o.rst_sys_n[0];
`endif
  clk_rst_if sys_clk_rst_if(.clk(sys_clk), .rst_n(sys_rst_n));

`ifdef GATE_LEVEL
  wire cpu_clk = `CPU_HIER.u_core.u_ibex_core.load_store_unit_i.ls_fsm_cs_reg_0_.CK;
`else
  wire cpu_clk = `CPU_HIER.clk_i;
`endif
  wire cpu_rst_n = `CPU_HIER.rst_ni;
  clk_rst_if cpu_clk_rst_if(.clk(cpu_clk), .rst_n(cpu_rst_n));

`ifdef GATE_LEVEL
  wire aon_clk = `CLKMGR_HIER.clocks_o_clk_aon_powerup;
  wire aon_rst_n = `RSTMGR_HIER.resets_o_rst_por_aon_n_0_;
`else
  wire aon_clk = `CLKMGR_HIER.clocks_o.clk_aon_powerup;
  wire aon_rst_n = `RSTMGR_HIER.resets_o.rst_por_aon_n[0];
`endif
  clk_rst_if aon_clk_por_rst_if(.clk(aon_clk), .rst_n(aon_rst_n));

  wire usb_clk = `USBDEV_HIER.clk_i;
  wire usb_rst_n = `USBDEV_HIER.rst_ni;
  clk_rst_if usb_clk_rst_if(.clk(usb_clk), .rst_n(usb_rst_n));

`ifdef GATE_LEVEL
  wire io_div4_clk = 1'b0;
  wire io_div4_rst_n = 1'b1;
`else
  wire io_div4_clk = `CLKMGR_HIER.clocks_o.clk_io_div4_powerup;
  wire io_div4_rst_n = `RSTMGR_HIER.resets_o.rst_por_io_div4_n[0];
`endif
  clk_rst_if io_div4_clk_rst_if(.clk(io_div4_clk), .rst_n(io_div4_rst_n));

`ifdef GATE_LEVEL
  wire lc_ready = 1'b0;
`else
  wire lc_ready = `LC_CTRL_HIER.u_reg.u_status_ready.qs;
`endif

  wire pwrmgr_low_power = `PWRMGR_HIER.low_power_o;
  wire pwrmgr_cpu_fetch_en = `PWRMGR_HIER.fetch_en_o == lc_ctrl_pkg::On;
  wire pwrmgr_fast_pwr_state_active = `PWRMGR_HIER.u_fsm.u_state_regs.state_o
      == pwrmgr_pkg::FastPwrStateActive;

`ifdef GATE_LEVEL
  wire rom_ctrl_done = 0;
  wire rom_ctrl_good = 0;

  wire rv_core_ibex_icache_otp_key_req = 0;
  wire rv_core_ibex_icache_otp_key_ack = 0;

  wire sram_main_init_done = 0;
  wire sram_ret_init_done = 0;

  wire flash_core1_host_req = 0;
`else
  wire rom_ctrl_done = `PWRMGR_HIER.rom_ctrl_i.done == prim_mubi_pkg::MuBi4True;
  wire rom_ctrl_good = `PWRMGR_HIER.rom_ctrl_i.good == prim_mubi_pkg::MuBi4True;

  wire rv_core_ibex_icache_otp_key_req = `RV_CORE_IBEX_HIER.icache_otp_key_o.req;
  wire rv_core_ibex_icache_otp_key_ack = `RV_CORE_IBEX_HIER.icache_otp_key_i.ack;

  wire sram_main_init_done = `SRAM_CTRL_MAIN_HIER.u_reg_regs.status_init_done_qs;
  wire sram_ret_init_done = `SRAM_CTRL_RET_HIER.u_reg_regs.status_init_done_qs;

  wire flash_core1_host_req = `FLASH_CTRL_HIER.u_eflash.gen_flash_cores[1].u_core.host_req_i;
`endif
  wire adc_data_valid = `AST_HIER.u_adc.adc_d_val_o;

  // alert_esc_if alert_if[NUM_ALERTS](.clk  (`ALERT_HANDLER_HIER.clk_i),
  //                                   .rst_n(`ALERT_HANDLER_HIER.rst_ni));
  // for (genvar i = 0; i < NUM_ALERTS; i++) begin : gen_alert_rx_conn
  //   assign alert_if[i].alert_rx = `ALERT_HANDLER_HIER.alert_rx_o[i];
  // end

  alerts_if alerts_if(.clk(`ALERT_HANDLER_HIER.clk_i), .rst_ni(`ALERT_HANDLER_HIER.rst_ni),
                      .alerts(`ALERT_HANDLER_HIER.alert_trig));

  // TODO: use pwrmgr_low_power, internal aon clk / rst monitor instead.
  pwrmgr_low_power_if pwrmgr_low_power_if(
`ifdef GATE_LEVEL
                                          .clk     (0),
                                          .fast_clk(0),
                                          .rst_n   (1)
`else
                                          .clk     (`CLKMGR_HIER.clocks_o.clk_aon_powerup),
                                          .fast_clk(`CLKMGR_HIER.clocks_o.clk_io_div4_powerup),
                                          .rst_n   (`RSTMGR_HIER.resets_o.rst_por_io_div4_n[0])
`endif
                                          );
  assign pwrmgr_low_power_if.low_power      = `PWRMGR_HIER.low_power_o;
  assign pwrmgr_low_power_if.in_sleep       = `PWRMGR_HIER.u_fsm.u_state_regs.state_o
                                            == pwrmgr_pkg::FastPwrStateLowPower;
`ifdef GATE_LEVEL
  assign pwrmgr_low_power_if.deep_powerdown = 0;
`else
  assign pwrmgr_low_power_if.deep_powerdown = ~`PWRMGR_HIER.pwr_ast_i.main_pok;
`endif
  // clkmgr related: SW controlled clock gating contol signals reflecting the actual status
  // of these clocks.
`ifdef GATE_LEVEL
  wire aes_clk_is_enabled = 0;
  wire hmac_clk_is_enabled = 0;
  wire kmac_clk_is_enabled = 0;
  wire otbn_clk_is_enabled = 0;

  wire usbdev_clk_is_enabled = 0;
  wire io_clk_is_enabled = 0;
  wire io_div2_clk_is_enabled = 0;
  wire io_div4_clk_is_enabled = 0;
`else
  wire aes_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_aes_val.d;
  wire hmac_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_hmac_val.d;
  wire kmac_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_kmac_val.d;
  wire otbn_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_otbn_val.d;

  wire usbdev_clk_is_enabled = `CLKMGR_HIER.u_reg.reg2hw.clk_enables.clk_usb_peri_en.q;
  wire io_clk_is_enabled = `CLKMGR_HIER.u_reg.reg2hw.clk_enables.clk_io_peri_en.q;
  wire io_div2_clk_is_enabled = `CLKMGR_HIER.u_reg.reg2hw.clk_enables.clk_io_div2_peri_en.q;
  wire io_div4_clk_is_enabled = `CLKMGR_HIER.u_reg.reg2hw.clk_enables.clk_io_div4_peri_en.q;
`endif
  // Ibex monitors.
  ibex_pkg::pmp_mseccfg_t pmp_mseccfg;
  ibex_pkg::pmp_cfg_t pmp_cfg[16];
  wire [31:0] pmp_addr[16];
  // TODO: merge with probed_cpu_csrs_t below.
`ifdef GATE_LEVEL
  assign pmp_mseccfg = 0;
  for(genvar i = 0; i < 16; i++) begin : gen_ibex_pmp_cfg_conn
    assign pmp_cfg[i] = 0;
    assign pmp_addr[i] = 0;
  end : gen_ibex_pmp_cfg_conn

  wire mstatus_mie = 0;
`else
  assign pmp_mseccfg = `IBEX_CSRS_HIER.g_pmp_registers.pmp_mseccfg_q;
  for(genvar i = 0; i < 16; i++) begin : gen_ibex_pmp_cfg_conn
    assign pmp_cfg[i] = `IBEX_CSRS_HIER.g_pmp_registers.pmp_cfg[i];
    assign pmp_addr[i] = `IBEX_CSRS_HIER.g_pmp_registers.pmp_addr[i];
  end : gen_ibex_pmp_cfg_conn

  wire mstatus_mie = `IBEX_CSRS_HIER.mstatus_q.mie;
`endif
  // Probed Ibex CSRs.
  typedef struct packed {
    logic [31:0][31:0] gprs;
    // Debug CSRs.
    jtag_rv_debugger_pkg::rv_core_csr_dcsr_t dcsr;
    logic [31:0] dpc;
    logic [31:0] dscratch0;
    logic [31:0] dscratch1;
    // Machine mode CSRs.
    logic [31:0] mstatus;
    logic [31:0] mepc;
    logic [31:0] mcause;
  } probed_cpu_csrs_t;
  wire probed_cpu_csrs_t probed_cpu_csrs;
  for (genvar i = 0; i < 32; i++) begin : gen_probed_cpu_csrs_conn
`ifdef GATE_LEVEL
    assign probed_cpu_csrs.gprs[i] = 0;
`else
    assign probed_cpu_csrs.gprs[i] = `CPU_CORE_HIER.gen_regfile_ff.register_file_i.rf_reg[i][31:0];
`endif
  end
  assign probed_cpu_csrs.dcsr = jtag_rv_debugger_pkg::rv_core_csr_dcsr_t'(
      `CPU_CORE_HIER.u_ibex_core.cs_registers_i.u_dcsr_csr.rd_data_o);
  assign probed_cpu_csrs.dpc =
      `CPU_CORE_HIER.u_ibex_core.cs_registers_i.u_depc_csr.rd_data_o;
  assign probed_cpu_csrs.dscratch0 =
      `CPU_CORE_HIER.u_ibex_core.cs_registers_i.u_dscratch0_csr.rd_data_o;
  assign probed_cpu_csrs.dscratch1 =
      `CPU_CORE_HIER.u_ibex_core.cs_registers_i.u_dscratch1_csr.rd_data_o;
  assign probed_cpu_csrs.mstatus =
      `CPU_CORE_HIER.u_ibex_core.cs_registers_i.u_mstatus_csr.rd_data_o;
  assign probed_cpu_csrs.mepc =
      `CPU_CORE_HIER.u_ibex_core.cs_registers_i.u_mepc_csr.rd_data_o;
  assign probed_cpu_csrs.mcause =
      `CPU_CORE_HIER.u_ibex_core.cs_registers_i.u_mcause_csr.rd_data_o;

  // Probed Ibex PC.
  typedef struct packed {
    logic [31:0] pc_if;
    logic [31:0] pc_id;
    logic [31:0] pc_wb;
  } probed_cpu_pc_t;
  wire probed_cpu_pc_t probed_cpu_pc;
 `ifndef GATE_LEVEL
  assign probed_cpu_pc.pc_if = `CPU_CORE_HIER.u_ibex_core.pc_if;
  assign probed_cpu_pc.pc_id = `CPU_CORE_HIER.u_ibex_core.pc_id;
  assign probed_cpu_pc.pc_wb = `CPU_CORE_HIER.u_ibex_core.pc_wb;
`endif
  // Stub CPU envorinment.
  //
  // The initial value is sought from a plusarg. It can however, be set by the sequence on the fly
  // as well. If enabled, the following things happen:
  // 1. The clock to the CPU is forced off.
  // 2. The address translation modules in rv_core_ibex are held in reset.
  // 3. The TL agent interface takes over the tl_d interface on the adapter.
  bit stub_cpu;
  tl_if cpu_d_tl_if(.clk(cpu_clk), .rst_n(cpu_rst_n));
`ifndef GATE_LEVEL
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
`endif
  // Pass interface handles to uvm_config_db.
  //
  // Since the chip_if handle itself will be passed to the chip env, there is no need to set
  // sub-interface handles that are consumed by the chip env. Only pass the sub-interface handles
  // for external interface agents.
  initial begin
    // TODO: Update once jtag_riscv_agent is replaced with jtag_dmi_agent / SBA accessor.
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_riscv_agent*", "vif", jtag_if);

    uvm_config_db#(virtual tl_if)::set(
        null, "*.env.m_tl_agent_chip_reg_block*", "vif", cpu_d_tl_if);

    // foreach (alert_if[i]) begin
    //   uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.m_alert_agent_%0s",
    //       LIST_OF_ALERTS[i]), "vif", alert_if[i]);
    // end
  end

  // Helper methods.

  // Disconnects all interfaces from chip IOs.
  //
  // Provides the test sequence a fresh start to connect specific interfaces needed by the test.
  // The por_n_if is exempt from this. The disconnection of default pulls using dios_if is
  // conditioned on the `disconnect_default_pulls` arg.
  function automatic void disconnect_all_interfaces(bit disconnect_default_pulls);
    `uvm_info(MsgId, "Disconnecting all interfaces from the chip IOs", UVM_LOW)
    if (disconnect_default_pulls) dios_if.disconnect();
    mios_if.disconnect();
    cc_if.disconnect();
    flash_test_volt_if.disconnect();
    flash_test_mode_if.disconnect();
    otp_ext_volt_if.disconnect();
    ec_rst_l_if.disconnect();
    flash_wp_l_if.disconnect();
    pwrb_in_if.disconnect();
    sysrst_ctrl_if.disconnect();
    ast_misc_if.disconnect();
    dft_straps_if.disconnect();
    tap_straps_if.disconnect();
    sw_straps_if.disconnect();
    gpios_if.disconnect();
    enable_flash_ctrl_jtag = 0;
    ast2pad_if.disconnect();
    pad2ast_if.disconnect();
    pinmux_wkup_if.disconnect();
    enable_spi_host = 1'b 0;
    for (int i = 0; i < NUM_UARTS; i++) enable_uart(.inst_num(i), .enable(0));
    for (int i = 0; i < NUM_SPI_HOSTS; i++) enable_spi_device(.inst_num(i), .enable(0));
    for (int i = 0; i < NUM_I2CS; i++) enable_i2c(.inst_num(i), .enable(0));
    ext_clk_if.set_active(0, 0);
  endfunction

  // Verifies an LC control signal broadcast by the LC controller.
  function automatic void check_lc_ctrl_enable_signal(lc_ctrl_signal_e signal, bit expected_value);
    lc_ctrl_pkg::lc_tx_t value;
    case (signal)
      LcCtrlSignalDftEn:        value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_dft_en_o);
      LcCtrlSignalNvmDebugEn:   value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_nvm_debug_en_o);
      LcCtrlSignalHwDebugEn:    value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_hw_debug_en_o);
      LcCtrlSignalCpuEn:        value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_cpu_en_o);
      LcCtrlSignalCreatorSeedEn: begin
        value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_creator_seed_sw_rw_en_o);
      end
      LcCtrlSignalOwnerSeedEn: begin
        value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_owner_seed_sw_rw_en_o);
      end
      LcCtrlSignalIsoRdEn:      value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_iso_part_sw_rd_en_o);
      LcCtrlSignalIsoWrEn:      value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_iso_part_sw_wr_en_o);
      LcCtrlSignalSeedRdEn:     value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_seed_hw_rd_en_o);
      LcCtrlSignalKeyMgrEn:     value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_keymgr_en_o);
      LcCtrlSignalEscEn:        value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_escalate_en_o);
      LcCtrlSignalCheckBypEn:   value = lc_ctrl_pkg::lc_tx_t'(`LC_CTRL_HIER.lc_check_byp_en_o);
      default:                  `uvm_fatal(MsgId, $sformatf("Bad choice: %0s", signal.name()))
    endcase
    if (expected_value ~^ (value == lc_ctrl_pkg::On)) begin
      `uvm_info(MsgId, $sformatf("LC control signal %0s: value = %0s matched",
                                 signal.name(), value.name()), UVM_HIGH)
    end else begin
      `uvm_error(MsgId, $sformatf("LC control signal %0s: value = %0s mismatched",
                                  signal.name(), value.name()))
    end
  endfunction

  // Verifies all LC control signals broadcast by the LC controller.
  function automatic void check_lc_ctrl_all_enable_signals(
      bit [LcCtrlSignalNumTotal-1:0] expected_values);
    foreach (expected_values[i]) begin
      check_lc_ctrl_enable_signal(lc_ctrl_signal_e'(i), expected_values[i]);
    end
  endfunction

  // Returns string path to an IP block instance.
  // TODO: Autogen this in top_<top>_pkg.
  function automatic string get_hier_path(top_earlgrey_pkg::peripheral_e peripheral);
    string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
    case (peripheral)
      PeripheralAdcCtrlAon:     path = {path, ".", `DV_STRINGIFY(`ADC_CTRL_HIER)};
      PeripheralAes:            path = {path, ".", `DV_STRINGIFY(`AES_HIER)};
      PeripheralAlertHandler:   path = {path, ".", `DV_STRINGIFY(`ALERT_HANDLER_HIER)};
      PeripheralAonTimerAon:    path = {path, ".", `DV_STRINGIFY(`AON_TIMER_HIER)};
      PeripheralAst:            path = {path, ".", `DV_STRINGIFY(`AST_HIER)};
      PeripheralClkmgrAon:      path = {path, ".", `DV_STRINGIFY(`CLKMGR_HIER)};
      PeripheralCsrng:          path = {path, ".", `DV_STRINGIFY(`CSRNG_HIER)};
      PeripheralEdn0:           path = {path, ".", `DV_STRINGIFY(`EDN_HIER(0))};
      PeripheralEdn1:           path = {path, ".", `DV_STRINGIFY(`EDN_HIER(1))};
      PeripheralEntropySrc:     path = {path, ".", `DV_STRINGIFY(`ENTROPY_SRC_HIER)};
      PeripheralFlashCtrl:      path = {path, ".", `DV_STRINGIFY(`FLASH_CTRL_HIER)};
      PeripheralGpio:           path = {path, ".", `DV_STRINGIFY(`GPIO_HIER)};
      PeripheralHmac:           path = {path, ".", `DV_STRINGIFY(`HMAC_HIER)};
      PeripheralI2c0:           path = {path, ".", `DV_STRINGIFY(`I2C_HIER(0))};
      PeripheralI2c1:           path = {path, ".", `DV_STRINGIFY(`I2C_HIER(1))};
      PeripheralI2c2:           path = {path, ".", `DV_STRINGIFY(`I2C_HIER(2))};
      PeripheralKeymgr:         path = {path, ".", `DV_STRINGIFY(`KEYMGR_HIER)};
      PeripheralKmac:           path = {path, ".", `DV_STRINGIFY(`KMAC_HIER)};
      PeripheralLcCtrl:         path = {path, ".", `DV_STRINGIFY(`LC_CTRL_HIER)};
      PeripheralOtbn:           path = {path, ".", `DV_STRINGIFY(`OTBN_HIER)};
      PeripheralOtpCtrl:        path = {path, ".", `DV_STRINGIFY(`OTP_CTRL_HIER)};
      PeripheralPattgen:        path = {path, ".", `DV_STRINGIFY(`PATTGEN_HIER)};
      PeripheralPinmuxAon:      path = {path, ".", `DV_STRINGIFY(`PINMUX_HIER)};
      PeripheralPwmAon:         path = {path, ".", `DV_STRINGIFY(`PWM_HIER)};
      PeripheralPwrmgrAon:      path = {path, ".", `DV_STRINGIFY(`PWRMGR_HIER)};
      PeripheralRomCtrl:        path = {path, ".", `DV_STRINGIFY(`ROM_CTRL_HIER)};
      PeripheralRstmgrAon:      path = {path, ".", `DV_STRINGIFY(`RSTMGR_HIER)};
      PeripheralRvCoreIbex:     path = {path, ".", `DV_STRINGIFY(`RV_CORE_IBEX_HIER)};
      PeripheralRvDm:           path = {path, ".", `DV_STRINGIFY(`RV_DM_HIER)};
      PeripheralRvPlic:         path = {path, ".", `DV_STRINGIFY(`RV_PLIC_HIER)};
      PeripheralRvTimer:        path = {path, ".", `DV_STRINGIFY(`RV_TIMER_HIER)};
      PeripheralSensorCtrlAon:  path = {path, ".", `DV_STRINGIFY(`SENSOR_CTRL_HIER)};
      PeripheralSpiDevice:      path = {path, ".", `DV_STRINGIFY(`SPI_DEVICE_HIER)};
      PeripheralSpiHost0:       path = {path, ".", `DV_STRINGIFY(`SPI_HOST_HIER(0))};
      PeripheralSpiHost1:       path = {path, ".", `DV_STRINGIFY(`SPI_HOST_HIER(1))};
      PeripheralSramCtrlMain:   path = {path, ".", `DV_STRINGIFY(`SRAM_CTRL_MAIN_HIER)};
      PeripheralSramCtrlRetAon: path = {path, ".", `DV_STRINGIFY(`SRAM_CTRL_RET_HIER)};
      PeripheralSysrstCtrlAon:  path = {path, ".", `DV_STRINGIFY(`SYSRST_CTRL_HIER)};
      PeripheralUart0:          path = {path, ".", `DV_STRINGIFY(`UART_HIER(0))};
      PeripheralUart1:          path = {path, ".", `DV_STRINGIFY(`UART_HIER(1))};
      PeripheralUart2:          path = {path, ".", `DV_STRINGIFY(`UART_HIER(2))};
      PeripheralUart3:          path = {path, ".", `DV_STRINGIFY(`UART_HIER(3))};
      PeripheralUsbdev:         path = {path, ".", `DV_STRINGIFY(`USBDEV_HIER)};
      default:      `uvm_fatal(MsgId, $sformatf("Bad peripheral: %0s", peripheral.name()))
    endcase
    return path;
  endfunction

  // Disable SVAs in certain hierarchies specific to tests.
  bit chip_padctrl_attributes_test_sva_disable;
  bit chip_sw_sleep_pin_mio_dio_val_sva_disable;

  /*
   * Helper methods for forcing internal signals.
   *
   * The macros invoked below create a static function to sample / force / release an internal
   * signal. Please see definition in `hw/dv/sv/dv_utils/dv_macros.svh` for more details.
   */

  // Signal probe function for LC program error signal in OTP ctrl.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_otp_ctrl_lc_err_o,
      `OTP_CTRL_HIER.u_otp_ctrl_lci.lc_err_o, 1)

  // Signal probe function for wait cycle mask in alert handler.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_alert_handler_ping_timer_wait_cyc_mask_i,
      `ALERT_HANDLER_HIER.u_ping_timer.wait_cyc_mask_i)

  // Signal probe function for keymgr key state.
`ifdef GATE_LEVEL
  bit dummy_signal_probe_keymgr_key_state;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_keymgr_key_state,
      dummy_signal_probe_keymgr_key_state)
`else
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_keymgr_key_state,
      `KEYMGR_HIER.u_ctrl.key_state_q)
`endif
  // Signal probe function for RX idle detection in usbdev.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_usbdev_rx_idle_det_o,
      `USBDEV_HIER.usbdev_impl.u_usb_fs_nb_pe.u_usb_fs_rx.rx_idle_det_o)

  // Signal probe function for se0 signal in usbdev.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_usbdev_se0,
      `USBDEV_HIER.usbdev_impl.u_usbdev_linkstate.line_se0_raw)

  // Signal probe function for link reset signal in usbdev.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_usbdev_link_reset_o,
      `USBDEV_HIER.usbdev_impl.u_usbdev_linkstate.link_reset_o)

  // Signal probe function for SOF valid signal in usbdev.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_usbdev_sof_valid_o,
      `USBDEV_HIER.usbdev_impl.u_usb_fs_nb_pe.sof_valid_o)

  // Signal probe function for peripheral to MIO in pinmux.
  wire [UVM_HDL_MAX_WIDTH-1:0] mio_to_periph = `PINMUX_HIER.mio_to_periph_o;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_mio_i,
      `PINMUX_HIER.periph_to_mio_i)

  // Signal probe function for peripheral to MIO output enable in pinmux.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_mio_oe_i,
      `PINMUX_HIER.periph_to_mio_oe_i)

  // Signal probe function for peripheral to DIO in pinmux.
  wire [UVM_HDL_MAX_WIDTH-1:0] dio_to_periph = `PINMUX_HIER.dio_to_periph_o;
  // We cannot force bits 12:13 since they are inputs. So we split the probe functions into two.
  // TODO: Find a more elegant solution for this.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_dio_i_11_0,
      `PINMUX_HIER.periph_to_dio_i[11:0])
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_dio_i_15_14,
      `PINMUX_HIER.periph_to_dio_i[15:14])

  // Signal probe function for peripheral to DIO output enable in pinmux.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_dio_oe_i,
      `PINMUX_HIER.periph_to_dio_oe_i)

  // Signal probe function for `vendor_test_ctrl` request from LC_CTRL to OTP_CTRL.
`ifdef GATE_LEVEL
  import otp_ctrl_pkg::*;
  bit dummy_signal_probe_otp_vendor_test_ctrl;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_otp_vendor_test_ctrl,
      dummy_signal_probe_otp_vendor_test_ctrl)
`else
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_otp_vendor_test_ctrl,
      `OTP_CTRL_HIER.lc_otp_vendor_test_i)
`endif
  /*
   * Signal probe functions for sampling the FSM states of the IPs
   * during the max power epoch of the power_virus test.
   */

  // Signal probe fuction for `fsm_state_q` of ADC_CTRL
  wire [4:0] adc_ctrl_state;
`ifdef GATE_LEVEL
`define _ADC_FSM_STATE_Q(i) \
   `ADC_CTRL_HIER.u_adc_ctrl_core.u_adc_ctrl_fsm.fsm_state_q_``i``_

  assign adc_ctrl_state = {`ADC_CTRL_HIER.u_adc_ctrl_core.u_adc_ctrl_fsm.fsm_state_q_CDR1_4_
                          ,`ADC_CTRL_HIER.u_adc_ctrl_core.u_adc_ctrl_fsm.fsm_state_q_CDR1_3_
                          ,`ADC_CTRL_HIER.u_adc_ctrl_core.u_adc_ctrl_fsm.fsm_state_q[2]
                          ,`ADC_CTRL_HIER.u_adc_ctrl_core.u_adc_ctrl_fsm.fsm_state_q_CDR1_1_
                          ,`ADC_CTRL_HIER.u_adc_ctrl_core.u_adc_ctrl_fsm.fsm_state_q[0]
                          };
`undef _ADC_FSM_STATE_Q
`else
  assign adc_ctrl_state = `ADC_CTRL_HIER.u_adc_ctrl_core.u_adc_ctrl_fsm.fsm_state_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_adc_ctrl_fsm_state,
      adc_ctrl_state, 5)

  // Signal probe function for `cio_csb_o` of SPI_HOST_0
  wire spi_host_0_cio_csb_o;
  assign spi_host_0_cio_csb_o = `SPI_HOST_HIER(0).cio_csb_o;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_spi_host_0_cio_csb_o,
      spi_host_0_cio_csb_o, 1)

  // Signal probe function for `cio_csb_i` of SPI_DEVICE
  wire spi_device_cio_csb_i;
  assign spi_device_cio_csb_i = `SPI_DEVICE_HIER.cio_csb_i;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_spi_device_cio_csb_i,
      spi_device_cio_csb_i, 1)

  // Signal probe function for `fsm.state_q` of SPI_HOST_1
  wire [2:0] spi_host_1_state;
`ifdef GATE_LEVEL
assign spi_host_1_state = {tb.dut.top_earlgrey.u_spi_host1.u_spi_core.u_fsm.state_q_reg_2_.Q
                          ,tb.dut.top_earlgrey.u_spi_host1.u_spi_core.u_fsm.state_q_reg_1_.Q
                          ,tb.dut.top_earlgrey.u_spi_host1.u_spi_core.u_fsm.state_q_reg_0_.Q
                          };
`else
  assign spi_host_1_state = `SPI_HOST_HIER(1).u_spi_core.u_fsm.state_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_spi_host_1_fsm_state,
      spi_host_1_state, 3)

  // Signal probe function for `acmd_q` of CSRNG core
  wire [2:0] csrng_acmd_q;
`ifdef GATE_LEVEL
  assign csrng_acmd_q = `CSRNG_HIER.u_csrng_core.acmd_q[2:0];
`else
  assign csrng_acmd_q = `CSRNG_HIER.u_csrng_core.acmd_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_csrng_acmd_q,
      csrng_acmd_q, 3)
  // Signal probe function for `rnd_ctr` of AES_CIPHER_CTRL
  wire [3:0] aes_ctrl_rnd_ctr;
  assign aes_ctrl_rnd_ctr =
`ifdef GATE_LEVEL
      `AES_HIER.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.mr_rnd_ctr[3:0];
`else
      `AES_HIER.u_aes_core.u_aes_cipher_core.u_aes_cipher_control.rnd_ctr;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_aes_ctrl_rnd_ctr,
      aes_ctrl_rnd_ctr, 4)

  // Signal probe function for `st_q` of HMAC
  wire [2:0] hmac_fsm_state;
`ifdef GATE_LEVEL
  assign hmac_fsm_state = {`HMAC_HIER.u_hmac.dftopt19
                          ,`HMAC_HIER.u_hmac.dftopt10
                          ,`HMAC_HIER.u_hmac.dftopt1
                          };
`else
  assign hmac_fsm_state = `HMAC_HIER.u_hmac.st_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_hmac_fsm_state,
      hmac_fsm_state, 3)

  // Signal probe function for `st` of KMAC_CORE
  wire [5:0] kmac_fsm_state;
  assign kmac_fsm_state = `KMAC_HIER.u_kmac_core.u_state_regs.state_o;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_kmac_fsm_state,
      kmac_fsm_state, 6)

  // Signal probe function for `state_q` OTBN_START_STOP_CONTROL
  wire [6:0] otbn_fsm_state;
  assign otbn_fsm_state = `OTBN_HIER.u_otbn_core.u_otbn_start_stop_control.u_state_regs.state_o;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_otbn_fsm_state,
      otbn_fsm_state, 7)

  // Signal probe function for `state_q` of EDN_0_MAIN_SM
  wire [8:0] edn_0_fsm_state;
`ifdef GATE_LEVEL
  assign edn_0_fsm_state = 0;
`else
  assign edn_0_fsm_state = `EDN_HIER(0).u_edn_core.u_edn_main_sm.state_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_edn_0_fsm_state,
      edn_0_fsm_state, 9)

  // Signal probe function for `state_q` of EDN_1_MAIN_SM
  wire [8:0] edn_1_fsm_state;
`ifdef GATE_LEVEL
  assign edn_1_fsm_state = 0;
`else
  assign edn_1_fsm_state = `EDN_HIER(1).u_edn_core.u_edn_main_sm.state_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_edn_1_fsm_state,
      edn_1_fsm_state, 9)

  // Signal probe function for `state_q` of ENTROPY_SOURCE_MAIN_SM
  wire [8:0] entropy_src_fsm_state;
`ifdef GATE_LEVEL
  assign entropy_src_fsm_state = 0;
`else
  assign entropy_src_fsm_state = `ENTROPY_SRC_HIER.u_entropy_src_core.u_entropy_src_main_sm.state_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_entropy_src_fsm_state,
      entropy_src_fsm_state, 9)

  // Signal probe function for `chan0.enable` and `chan1.enable`of PATTGEN
  wire [1:0] pattgen_chan_1_0_enable;
`ifdef GATE_LEVEL
  assign pattgen_chan_1_0_enable = {`PATTGEN_HIER.u_pattgen_core.chan1.ctrl_i_enable
                                   ,`PATTGEN_HIER.u_pattgen_core.chan0.ctrl_i_enable};
`else
  assign pattgen_chan_1_0_enable = {`PATTGEN_HIER.u_pattgen_core.chan1.enable,
                                    `PATTGEN_HIER.u_pattgen_core.chan0.enable};
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pattgen_chan_1_0_enable,
      pattgen_chan_1_0_enable, 2)

  // tb.dut.top_earlgrey.u_pwm_aon.u_pwm_core.cntr_en
  wire pwm_core_cntr_en;
`ifdef GATE_LEVEL
  assign pwm_core_cntr_en = `PWM_HIER.u_reg.u_cfg_cntr_en.q;
`else
  assign pwm_core_cntr_en = `PWM_HIER.u_pwm_core.cntr_en;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pwm_core_cntr_en,
      pwm_core_cntr_en, 1)

`undef TOP_HIER
`undef ADC_CTRL_HIER
`undef AES_HIER
`undef AES_CONTROL_HIER
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
`undef RV_CORE_IBEX_HIER
`undef RV_DM_HIER
`undef RV_PLIC_HIER
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
