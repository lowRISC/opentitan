// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// One chip level interface to rule them all, and in the IOs, bind them...
//
// The top_darjeeling SoC provides a bunch of fixed-function and muxed IO pads. The interface serves
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
  import top_darjeeling_pkg::*;
  import dv_utils_pkg::*;
  import uvm_pkg::*;

  `include "dv_macros.svh"
  `include "uvm_macros.svh"

  // TODO: Move these to `include "./chip_hier_macros.svh". Deprecate ../tb/chip_hier_macros.svh.
  // TODO: In Xcelium, the bind is not exposing the internal hierarchies to chip_if.
  // TODO: Autogen this in top_<top>_pkg.
`ifdef XCELIUM
  `define TOP_HIER          tb.dut.top_darjeeling
`else
  `define TOP_HIER          top_darjeeling
`endif
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
`define EDN_HIER(i)         `TOP_HIER.u_edn``i
`define GPIO_HIER           `TOP_HIER.u_gpio
`define HMAC_HIER           `TOP_HIER.u_hmac
`define I2C_HIER(i)         `TOP_HIER.u_i2c``i
`define IBEX_HIER           `CPU_CORE_HIER.u_ibex_core
`define IBEX_CSRS_HIER      `IBEX_HIER.cs_registers_i
`define KMAC_HIER           `TOP_HIER.u_kmac
`define KEYMGR_DPE_HIER     `TOP_HIER.u_keymgr_dpe
`define LC_CTRL_HIER        `TOP_HIER.u_lc_ctrl
`define OTBN_HIER           `TOP_HIER.u_otbn
`define OTP_CTRL_HIER       `TOP_HIER.u_otp_ctrl
`define OTP_MACRO_HIER      `TOP_HIER.u_otp_macro
`define PINMUX_HIER         `TOP_HIER.u_pinmux_aon
`define PWRMGR_HIER         `TOP_HIER.u_pwrmgr_aon
`define ROM_CTRL0_HIER      `TOP_HIER.u_rom_ctrl0
`define ROM_CTRL1_HIER      `TOP_HIER.u_rom_ctrl1
`define RSTMGR_HIER         `TOP_HIER.u_rstmgr_aon
`define RV_CORE_IBEX_HIER   `TOP_HIER.u_rv_core_ibex
`define RV_DM_HIER          `TOP_HIER.u_rv_dm
`define RV_PLIC_HIER        `TOP_HIER.u_rv_plic
`define RV_TIMER_HIER       `TOP_HIER.u_rv_timer
`define SENSOR_CTRL_HIER    `TOP_HIER.u_sensor_ctrl
`define SOC_PROXY_HIER      `TOP_HIER.u_soc_proxy
`define SPI_DEVICE_HIER     `TOP_HIER.u_spi_device
`define SPI_HOST_HIER(i)    `TOP_HIER.u_spi_host``i
`define SRAM_CTRL_MAIN_HIER `TOP_HIER.u_sram_ctrl_main
`define SRAM_CTRL_RET_HIER  `TOP_HIER.u_sram_ctrl_ret_aon
`define SRAM_CTRL_MBOX      `TOP_HIER.u_sram_ctrl_mbox
`define UART_HIER(i)        `TOP_HIER.u_uart``i

  // Identifier for logs.
  string MsgId = $sformatf("%m");

  // Identifier for the envorinment to which this interface is passed on via uvm_config_db.
  string env_name = "env";

  // Directly connected to chip IOs.
  //
  // DO NOT manipulate this signal in test sequences directly. Use the individual functional
  // interfaces below instead.
  wire [top_darjeeling_pkg::DioPadCount-1:0] dios;
  wire [top_darjeeling_pkg::MioPadCount-1:0] mios;

  // Functional interface: for testing ALL chip IOs, such as pinmux and padctrl tests.
  pins_if#(.Width(top_darjeeling_pkg::MioPadCount), .PullStrength("Weak")) mios_if(.pins(mios));
  pins_if#(.Width(top_darjeeling_pkg::DioPadCount), .PullStrength("Weak")) dios_if(.pins(dios));

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
      dios_if.pins_pu[top_darjeeling_pkg::DioPadPorN] = 1;

      // No need of pulls for the SPI host peripheral.
      dios_if.pins_pd[top_darjeeling_pkg::DioPadSpiHostCsL:top_darjeeling_pkg::DioPadSpiHostD0]
          = '0;
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
  for (genvar i = top_darjeeling_pkg::MioPadMio0; i < top_darjeeling_pkg::MioPadCount; i++)
  begin : gen_mios_x_check
    wire glitch_free_io;
    assign #1ps glitch_free_io = mios[i];

    top_darjeeling_pkg::mio_pad_e named_io = top_darjeeling_pkg::mio_pad_e'(i);
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
  pins_if #(.Width(1), .PullStrength("Weak")) por_n_if(.pins(dios[top_darjeeling_pkg::DioPadPorN]));

  // Functional (dedicated) interface (analog input): OTP ext volt.
  pins_if #(.Width(1), .PullStrength("Weak")) otp_ext_volt_if(
    .pins(dios[top_darjeeling_pkg::DioPadOtpExtVolt])
  );

  // Functional (dedicated) interface: SPI host interface (drives traffic into the chip).
  bit enable_spi_host = 1;
  bit enable_spi_tpm;
  spi_if spi_host_if(
    .rst_n(`SPI_DEVICE_HIER.rst_ni),
    .sio  (dios[top_darjeeling_pkg::DioPadSpiDevD3:top_darjeeling_pkg::DioPadSpiDevD0])
  );
  assign dios[top_darjeeling_pkg::DioPadSpiDevClk] = enable_spi_host | enable_spi_tpm ?
      spi_host_if.sck : 1'bz;
  assign dios[top_darjeeling_pkg::DioPadSpiDevCsL] = enable_spi_host ? spi_host_if.csb[0] : 1'bz;
  assign dios[top_darjeeling_pkg::DioPadSpiDevTpmCsL] = enable_spi_tpm ? spi_host_if.csb[1] : 1'bz;
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
    .sio  (dios[top_darjeeling_pkg::DioPadSpiHostD3:
                top_darjeeling_pkg::DioPadSpiHostD0])
  );

  assign spi_device0_if.sck = __enable_spi_device[0] ?
      dios[top_darjeeling_pkg::DioPadSpiHostClk] : 1'bz;

  assign spi_device0_if.csb = __enable_spi_device[0] ?
      {'1, dios[top_darjeeling_pkg::DioPadSpiHostCsL]} : '1;

  initial begin
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_device_agents0*", "vif", spi_device0_if);
    do begin
      spi_device0_if.disconnect(!__enable_spi_device[0]);
      @(__enable_spi_device[0]);
    end while(1);
  end

  // Enables tb spi_device, which connects to dut spi_host
  function automatic void enable_spi_device(int inst_num, bit enable);
    `DV_CHECK_FATAL(inst_num inside {[0:NUM_SPI_HOSTS-1]}, , MsgId)
    `uvm_info(MsgId, $sformatf("enable spi device %0d", inst_num), UVM_LOW)
    __enable_spi_device[inst_num] = enable;
  endfunction : enable_spi_device

  // Functional (muxed) interface: SW straps.
  pins_if #(.Width(3), .PullStrength("Weak")) sw_straps_if(
    .pins(dios[top_darjeeling_pkg::DioPadGpio24:top_darjeeling_pkg::DioPadGpio22])
  );

  // Functional (muxed) interface: GPIOs.
  //
  // The pins allocated for GPIOs overlap with several other functions, but that is ok. For pre-Si
  // DV, the directed tests that verify the GPIOs are not likely to also enable other functions that
  // overlap with these pins. If they do, we could set masks and limit the GPIOs to a smaller
  // subset. The selection below prevents as much contention as possible on the IOs, considering
  // various modes the testbench AND the device can be in.
  pins_if #(.Width(NUM_GPIOS), .PullStrength("Weak")) gpios_if(
    .pins({dios[top_darjeeling_pkg::DioPadGpio31], dios[top_darjeeling_pkg::DioPadGpio30],
           dios[top_darjeeling_pkg::DioPadGpio29], dios[top_darjeeling_pkg::DioPadGpio28],
           dios[top_darjeeling_pkg::DioPadGpio27], dios[top_darjeeling_pkg::DioPadGpio26],
           dios[top_darjeeling_pkg::DioPadGpio25], dios[top_darjeeling_pkg::DioPadGpio24],
           dios[top_darjeeling_pkg::DioPadGpio23], dios[top_darjeeling_pkg::DioPadGpio22],
           dios[top_darjeeling_pkg::DioPadGpio21], dios[top_darjeeling_pkg::DioPadGpio20],
           dios[top_darjeeling_pkg::DioPadGpio19], dios[top_darjeeling_pkg::DioPadGpio18],
           dios[top_darjeeling_pkg::DioPadGpio17], dios[top_darjeeling_pkg::DioPadGpio16],
           dios[top_darjeeling_pkg::DioPadGpio15], dios[top_darjeeling_pkg::DioPadGpio14],
           dios[top_darjeeling_pkg::DioPadGpio13], dios[top_darjeeling_pkg::DioPadGpio12],
           dios[top_darjeeling_pkg::DioPadGpio11], dios[top_darjeeling_pkg::DioPadGpio10],
           dios[top_darjeeling_pkg::DioPadGpio9],  dios[top_darjeeling_pkg::DioPadGpio8],
           dios[top_darjeeling_pkg::DioPadGpio7],  dios[top_darjeeling_pkg::DioPadGpio6],
           dios[top_darjeeling_pkg::DioPadGpio5],  dios[top_darjeeling_pkg::DioPadGpio4],
           dios[top_darjeeling_pkg::DioPadGpio3],  dios[top_darjeeling_pkg::DioPadGpio2],
           dios[top_darjeeling_pkg::DioPadGpio1],  dios[top_darjeeling_pkg::DioPadGpio0]})
  );

  // Functional (dedicated) interface: JTAG (valid during debug enabled LC state only).
  // JTAG has dedicated pads for darjeeling, so leave it always enabled.
  wire __enable_jtag = 1'b1;
  jtag_if jtag_if();

  wire dmi_clk = `CLKMGR_HIER.clocks_o.clk_main_infra;
  wire dmi_rst_n = `RSTMGR_HIER.resets_o.rst_lc_n[0];
  clk_rst_if dmi_clk_rst_if(.clk(dmi_clk), .rst_n(dmi_rst_n));
  tl_if dmi_tl_if(.clk(dmi_clk), .rst_n(dmi_rst_n));

  function automatic void configure_jtag_dmi(bit use_jtag_dmi);
`ifndef GATE_LEVEL
    if (use_jtag_dmi) begin
      force dmi_tl_if.h2d = `TOP_HIER.dbg_tl_req_i;
      force dmi_tl_if.d2h = `TOP_HIER.dbg_tl_rsp_o;
    end else begin
      force `TOP_HIER.dbg_tl_req_i = dmi_tl_if.h2d;
      force dmi_tl_if.d2h = `TOP_HIER.dbg_tl_rsp_o;
    end
`endif
  endfunction

  assign dios[top_darjeeling_pkg::DioPadJtagTms] = __enable_jtag ? jtag_if.tms : 1'bz;
  assign jtag_if.tdo = __enable_jtag ? dios[top_darjeeling_pkg::DioPadJtagTdo] : 1'bz;
  assign dios[top_darjeeling_pkg::DioPadJtagTdi] = __enable_jtag ? jtag_if.tdi : 1'bz;
  assign dios[top_darjeeling_pkg::DioPadJtagTck] = __enable_jtag ? jtag_if.tck : 1'bz;
  assign dios[top_darjeeling_pkg::DioPadJtagTrstN] = __enable_jtag ? jtag_if.trst_n : 1'bz;

  function automatic void set_tdo_pull(bit value);
    if (value) begin
      dios_if.pins_pd[top_darjeeling_pkg::DioPadJtagTdo] = 0;
      dios_if.pins_pu[top_darjeeling_pkg::DioPadJtagTdo] = 1;
    end else begin
      dios_if.pins_pd[top_darjeeling_pkg::DioPadJtagTdo] = 1;
      dios_if.pins_pu[top_darjeeling_pkg::DioPadJtagTdo] = 0;
    end
  endfunction

  // Sampled lc_hw_debug_en in RV_DM.
  wire rv_dm_lc_hw_debug_en =
    (`RV_DM_HIER.gen_dmi_gating.u_rv_dm_dmi_gate.u_prim_lc_sync_strap_hw_debug_en.lc_en_o ==
     lc_ctrl_pkg::On);

  // Functional (dedicated) interface: Pin wake up signal.
  // TODO: For these tests, use chip_pins_if instead, so that any pin can be configured to wakeup.
  pins_if #(.Width(1), .PullStrength("Weak")) pinmux_wkup_if(
    .pins(dios[top_darjeeling_pkg::DioPadGpio0])
  );

  // Functional (dedicated) interface: UARTs.
  localparam int AssignedUartTxIos[NUM_UARTS] = {
      top_darjeeling_pkg::DioPadUartTx
  };
  localparam int AssignedUartRxIos[NUM_UARTS] = {
      top_darjeeling_pkg::DioPadUartRx
  };
  bit [NUM_UARTS-1:0] __enable_uart;  // Internal signal.

  for (genvar i = 0; i < NUM_UARTS; i++) begin : gen_uart_if_conn
    uart_if uart_if();
    assign dios[AssignedUartRxIos[i]] = __enable_uart[i] ? uart_if.uart_rx : 1'bz;
    assign uart_if.uart_tx = __enable_uart[i] ? dios[AssignedUartTxIos[i]] : 1'b1;

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
    dios_if.pins_pu[AssignedUartTxIos[inst_num]] = enable;
    dios_if.pins_pu[AssignedUartRxIos[inst_num]] = enable;
    __enable_uart[inst_num] = enable;
  endfunction


  // Functional (dedicated) interface: I2Cs.
  bit [NUM_I2CS-1:0] __enable_i2c = {NUM_I2CS{1'b0}}; // Internal signal.

  // {ioa7, ioa8} are the i2c0 connections
  localparam int AssignedI2cSclIos [NUM_I2CS]  = {
    top_darjeeling_pkg::DioPadI2cScl
  };
  localparam int AssignedI2cSdaIos [NUM_I2CS] = {
    top_darjeeling_pkg::DioPadI2cSda
  };

  // This part unfortunately has to be hardcoded since the macro cannot interpret a genvar.
  wire [NUM_I2CS-1:0]i2c_clks = {`I2C_HIER(0).clk_i};
  wire [NUM_I2CS-1:0]i2c_rsts = {`I2C_HIER(0).rst_ni};

  for (genvar i = 0; i < NUM_I2CS; i++) begin : gen_i2c_if
    i2c_if i2c_if(
      .clk_i(i2c_clks[i]),
      .rst_ni(i2c_rsts[i]),
      .scl_io(dios[AssignedI2cSclIos[i]]),
      .sda_io(dios[AssignedI2cSdaIos[i]])
    );

    // connect to agents
    initial begin
      uvm_config_db#(virtual i2c_if)::set(null, $sformatf("*.env.m_i2c_agent%0d*", i),
      "vif", i2c_if);
    end
  end

  function automatic void enable_i2c(int inst_num, bit enable);
    `DV_CHECK_FATAL(inst_num inside {[0:NUM_I2CS-1]}, , MsgId)
    dios_if.pins_pu[AssignedI2cSclIos[inst_num]] = enable;
    dios_if.pins_pd[AssignedI2cSclIos[inst_num]] = 0;
    dios_if.pins_pu[AssignedI2cSdaIos[inst_num]] = enable;
    dios_if.pins_pd[AssignedI2cSdaIos[inst_num]] = 0;
    __enable_i2c[inst_num] = enable;
  endfunction

  /////////////////////////////////////////////////
  // Functional (dedicated) interfaces: mailbox(es)
  //
  // The TB currently instantiates 'chip_darjeeling_asic' as the DUT, but this does not
  // patch-through the mailbox interfaces. For now, use hierarchical references to
  // connect to these signals.

  wire mbx_if_clk = `TOP_HIER.clkmgr_aon_clocks.clk_main_infra;
  wire mbx_if_rst_n = `TOP_HIER.rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel];
  wire mbx_intr_signals_t[NUM_MBXS-1:0] mbx_interrupts;
  mbx_if darjeeling_mbx_if(.clk(mbx_if_clk), .rst_n(mbx_if_rst_n));
  function automatic void connect_mbx_if();
    force darjeeling_mbx_if.interrupts    = mbx_interrupts;
    force darjeeling_mbx_if.mbx_tl_if.d2h = `TOP_HIER.mbx_tl_rsp_o;
    force `TOP_HIER.mbx_tl_req_i          = darjeeling_mbx_if.mbx_tl_if.h2d;
  endfunction
  function automatic void disconnect_mbx_if();
    release darjeeling_mbx_if.interrupts;
    release darjeeling_mbx_if.mbx_tl_if.d2h;
    release `TOP_HIER.mbx_tl_req_i;
  endfunction

  // All of the mailbox signals egressing the design have unique names, which makes the
  // process of assigning them to interfaces not ergonomic.
  // TODO: Macroize / autogen alias array which can be iterated over
  assign mbx_interrupts = '{
    '{`TOP_HIER.mbx_pcie1_doe_intr_o,
      `TOP_HIER.mbx_pcie1_doe_intr_en_o,
      `TOP_HIER.mbx_pcie1_doe_intr_support_o,
      `TOP_HIER.mbx_pcie1_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx_pcie0_doe_intr_o,
      `TOP_HIER.mbx_pcie0_doe_intr_en_o,
      `TOP_HIER.mbx_pcie0_doe_intr_support_o,
      `TOP_HIER.mbx_pcie0_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx_jtag_doe_intr_o,
      `TOP_HIER.mbx_jtag_doe_intr_en_o,
      `TOP_HIER.mbx_jtag_doe_intr_support_o,
      `TOP_HIER.mbx_jtag_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx6_doe_intr_o,
      `TOP_HIER.mbx6_doe_intr_en_o,
      `TOP_HIER.mbx6_doe_intr_support_o,
      `TOP_HIER.mbx6_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx5_doe_intr_o,
      `TOP_HIER.mbx5_doe_intr_en_o,
      `TOP_HIER.mbx5_doe_intr_support_o,
      `TOP_HIER.mbx5_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx4_doe_intr_o,
      `TOP_HIER.mbx4_doe_intr_en_o,
      `TOP_HIER.mbx4_doe_intr_support_o,
      `TOP_HIER.mbx4_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx3_doe_intr_o,
      `TOP_HIER.mbx3_doe_intr_en_o,
      `TOP_HIER.mbx3_doe_intr_support_o,
      `TOP_HIER.mbx3_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx2_doe_intr_o,
      `TOP_HIER.mbx2_doe_intr_en_o,
      `TOP_HIER.mbx2_doe_intr_support_o,
      `TOP_HIER.mbx2_doe_async_msg_support_o
      },
    '{`TOP_HIER.mbx1_doe_intr_o,
      `TOP_HIER.mbx1_doe_intr_en_o,
      `TOP_HIER.mbx1_doe_intr_support_o,
      `TOP_HIER.mbx1_doe_async_msg_support_o
      }, // [1]
    '{`TOP_HIER.mbx0_doe_intr_o,               // [3]
      `TOP_HIER.mbx0_doe_intr_en_o,            // [2]
      `TOP_HIER.mbx0_doe_intr_support_o,       // [1]
      `TOP_HIER.mbx0_doe_async_msg_support_o   // [0]
      }  // [0]
    };

  ///////////////////////////////////////////////////////
  // Functional (muxed) interface: external clock source.
  //
  // The reset port is passive only.
  clk_rst_if#("ExtClkDriver") ext_clk_if(
     .clk (mios[top_darjeeling_pkg::MioPadMio11]),
    .rst_n(dios[top_darjeeling_pkg::DioPadPorN])
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
  wire aon_clk = 1'b0;
  wire aon_rst_n = 1'b1;
`else
  wire aon_clk = `CLKMGR_HIER.clocks_o.clk_aon_powerup;
  wire aon_rst_n = `RSTMGR_HIER.resets_o.rst_por_aon_n[0];
`endif
  clk_rst_if aon_clk_por_rst_if(.clk(aon_clk), .rst_n(aon_rst_n));

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
  wire lc_ready = `LC_CTRL_HIER.u_reg_regs.u_status_ready.qs;
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
  wire sram_mbox_init_done = 0;
`else
  wire rom_ctrl_done = `PWRMGR_HIER.rom_ctrl_done_combined == prim_mubi_pkg::MuBi4True;
  wire rom_ctrl_good = `PWRMGR_HIER.rom_ctrl_good_combined == prim_mubi_pkg::MuBi4True;

  wire rv_core_ibex_icache_otp_key_req = `RV_CORE_IBEX_HIER.icache_otp_key_o.req;
  wire rv_core_ibex_icache_otp_key_ack = `RV_CORE_IBEX_HIER.icache_otp_key_i.ack;

  wire sram_main_init_done = `SRAM_CTRL_MAIN_HIER.u_reg_regs.status_init_done_qs;
  wire sram_ret_init_done = `SRAM_CTRL_RET_HIER.u_reg_regs.status_init_done_qs;
  wire sram_mbox_init_done = `SRAM_CTRL_MBOX.u_reg_regs.status_init_done_qs;
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

  wire io_clk_is_enabled = 0;
  wire io_div2_clk_is_enabled = 0;
  wire io_div4_clk_is_enabled = 0;
`else
  wire aes_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_aes_val.d;
  wire hmac_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_hmac_val.d;
  wire kmac_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_kmac_val.d;
  wire otbn_clk_is_enabled = `CLKMGR_HIER.u_reg.hw2reg.clk_hints_status.clk_main_otbn_val.d;

// TODO: Not used in DV simulation.
// wire io_clk_is_enabled = `CLKMGR_HIER.u_reg.reg2hw.clk_enables.clk_io_peri_en.q;
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
  // Stub CPU environment.
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

    uvm_config_db#(virtual tl_if)::set(
        null, "*.env.m_tl_agent_chip_soc_dbg_reg_block*", "vif", dmi_tl_if);
    uvm_config_db#(virtual tl_if)::set(
        null, "*.env.m_tl_agent_chip_soc_mbx_reg_block*", "vif", darjeeling_mbx_if.mbx_tl_if);

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
    disconnect_mbx_if();
    otp_ext_volt_if.disconnect();
    sw_straps_if.disconnect();
    gpios_if.disconnect();
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
  function automatic string get_hier_path(top_darjeeling_pkg::peripheral_e peripheral);
    string path = dv_utils_pkg::get_parent_hier($sformatf("%m"));
    case (peripheral)
      PeripheralAes:            path = {path, ".", `DV_STRINGIFY(`AES_HIER)};
      PeripheralAlertHandler:   path = {path, ".", `DV_STRINGIFY(`ALERT_HANDLER_HIER)};
      PeripheralAonTimerAon:    path = {path, ".", `DV_STRINGIFY(`AON_TIMER_HIER)};
      PeripheralAst:            path = {path, ".", `DV_STRINGIFY(`AST_HIER)};
      PeripheralClkmgrAon:      path = {path, ".", `DV_STRINGIFY(`CLKMGR_HIER)};
      PeripheralCsrng:          path = {path, ".", `DV_STRINGIFY(`CSRNG_HIER)};
      PeripheralEdn0:           path = {path, ".", `DV_STRINGIFY(`EDN_HIER(0))};
      PeripheralEdn1:           path = {path, ".", `DV_STRINGIFY(`EDN_HIER(1))};
      PeripheralGpio:           path = {path, ".", `DV_STRINGIFY(`GPIO_HIER)};
      PeripheralHmac:           path = {path, ".", `DV_STRINGIFY(`HMAC_HIER)};
      PeripheralI2c0:           path = {path, ".", `DV_STRINGIFY(`I2C_HIER(0))};
      PeripheralKeymgrDpe:      path = {path, ".", `DV_STRINGIFY(`KEYMGR_DPE_HIER)};
      PeripheralKmac:           path = {path, ".", `DV_STRINGIFY(`KMAC_HIER)};
      PeripheralLcCtrl:         path = {path, ".", `DV_STRINGIFY(`LC_CTRL_HIER)};
      PeripheralOtbn:           path = {path, ".", `DV_STRINGIFY(`OTBN_HIER)};
      PeripheralOtpCtrl:        path = {path, ".", `DV_STRINGIFY(`OTP_CTRL_HIER)};
      PeripheralPinmuxAon:      path = {path, ".", `DV_STRINGIFY(`PINMUX_HIER)};
      PeripheralPwrmgrAon:      path = {path, ".", `DV_STRINGIFY(`PWRMGR_HIER)};
      PeripheralRomCtrl0:       path = {path, ".", `DV_STRINGIFY(`ROM_CTRL0_HIER)};
      PeripheralRomCtrl1:       path = {path, ".", `DV_STRINGIFY(`ROM_CTRL1_HIER)};
      PeripheralRstmgrAon:      path = {path, ".", `DV_STRINGIFY(`RSTMGR_HIER)};
      PeripheralRvCoreIbex:     path = {path, ".", `DV_STRINGIFY(`RV_CORE_IBEX_HIER)};
      PeripheralRvDm:           path = {path, ".", `DV_STRINGIFY(`RV_DM_HIER)};
      PeripheralRvPlic:         path = {path, ".", `DV_STRINGIFY(`RV_PLIC_HIER)};
      PeripheralRvTimer:        path = {path, ".", `DV_STRINGIFY(`RV_TIMER_HIER)};
      PeripheralSpiDevice:      path = {path, ".", `DV_STRINGIFY(`SPI_DEVICE_HIER)};
      PeripheralSpiHost0:       path = {path, ".", `DV_STRINGIFY(`SPI_HOST_HIER(0))};
      PeripheralSramCtrlMain:   path = {path, ".", `DV_STRINGIFY(`SRAM_CTRL_MAIN_HIER)};
      PeripheralSramCtrlRetAon: path = {path, ".", `DV_STRINGIFY(`SRAM_CTRL_RET_HIER)};
      PeripheralUart0:          path = {path, ".", `DV_STRINGIFY(`UART_HIER(0))};
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

  // TODO(#462): Decide if we need this probing function (only used in alert handler escalation
  // sequence)
  // Signal probe function for keymgr key state.
  // `ifdef GATE_LEVEL
  //   bit dummy_signal_probe_keymgr_key_state;
  //   `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_keymgr_key_state,
  //       dummy_signal_probe_keymgr_key_state)
  // `else
  //   `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_keymgr_key_state,
  //       `KEYMGR_DPE_HIER.u_ctrl.key_state_q)
  // `endif

  // Signal probe function for peripheral to MIO in pinmux.
  wire [UVM_HDL_MAX_WIDTH-1:0] mio_to_periph = `PINMUX_HIER.mio_to_periph_o;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_mio_i,
      `PINMUX_HIER.periph_to_mio_i)

  // Signal probe function for peripheral to MIO output enable in pinmux.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_mio_oe_i,
      `PINMUX_HIER.periph_to_mio_oe_i)

  // Signal probe function for peripheral to DIO in pinmux.
  wire [UVM_HDL_MAX_WIDTH-1:0] dio_to_periph = `PINMUX_HIER.dio_to_periph_o;
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pinmux_periph_to_dio_i_11_0,
      `PINMUX_HIER.periph_to_dio_i[11:0])

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
      `OTP_MACRO_HIER.test_i)
`endif
  /*
   * Signal probe functions for sampling the FSM states of the IPs
   * during the max power epoch of the power_virus test.
   */

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

  // Signal probe function for `state_q` of CSRNG main FSM
  wire [csrng_pkg::MainSmStateWidth-1:0] csrng_main_state;
`ifdef GATE_LEVEL
  assign csrng_main_state = 0;
`else
  assign csrng_main_state = `CSRNG_HIER.u_csrng_core.u_csrng_main_sm.state_q;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_csrng_main_fsm_state,
      csrng_main_state, csrng_pkg::MainSmStateWidth)
  // Signal probe function for `aes_ctrl_cs` of AES_CTRL_FSM
  wire [5:0] aes_ctrl_fsm_state;
  assign aes_ctrl_fsm_state =
`ifdef GATE_LEVEL
                             0;
`else
      `AES_CONTROL_HIER.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.u_aes_control_fsm.aes_ctrl_cs;
`endif
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_aes_ctrl_fsm_state,
      aes_ctrl_fsm_state, 6)

  // Signal probe function for `st_q` of HMAC
  wire [2:0] hmac_fsm_state;
`ifdef GATE_LEVEL
  assign hmac_fsm_state = {`HMAC_HIER.u_hmac.st_q_reg_2_.Q
                          ,`HMAC_HIER.u_hmac.st_q_reg_1_.Q
                          ,`HMAC_HIER.u_hmac.st_q_reg_0_.Q
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

  // Signal probe function for `wkup_internal_req_o` of SOC_PROXY_HIER
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_proxy_wkup_internal_req,
                                   `SOC_PROXY_HIER.wkup_internal_req_o,
                                   1)

  // Signal probe function for `soc_intr_async_i` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_intr_async,
                                   `TOP_HIER.soc_intr_async_i,
                                   soc_proxy_reg_pkg::NumExternalIrqs)

  // Signal probe function for `soc_fatal_alert_req` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_fatal_alert_req,
                                   `TOP_HIER.soc_fatal_alert_req_i,
                                   2 * soc_proxy_pkg::NumFatalExternalAlerts)

  // Signal probe function for `soc_fatal_alert_rsp` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_fatal_alert_rsp,
                                   `TOP_HIER.soc_fatal_alert_rsp_o,
                                   2 * soc_proxy_pkg::NumFatalExternalAlerts)

  // Signal probe function for `soc_gpi_async_o` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_gpi_async,
                                   `TOP_HIER.soc_gpi_async_o,
                                   soc_proxy_pkg::NumSocGpio)

  // Signal probe function for `soc_gpo_async_i` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_gpo_async,
                                   `TOP_HIER.soc_gpo_async_i,
                                   soc_proxy_pkg::NumSocGpio)

  // Signal probe function for `soc_recov_alert_req` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_recov_alert_req,
                                   `TOP_HIER.soc_recov_alert_req_i,
                                   2 * soc_proxy_pkg::NumRecovExternalAlerts)

  // Signal probe function for `soc_recov_alert_rsp` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_recov_alert_rsp,
                                   `TOP_HIER.soc_recov_alert_rsp_o,
                                   2 * soc_proxy_pkg::NumRecovExternalAlerts)

  // Signal probe function for `boot_status.light_reset_req` of TOP_HIER.
  // This shall only be used as a probe, not a driver.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_pwrmgr_light_reset_req,
                                   `TOP_HIER.pwrmgr_boot_status_o.light_reset_req,
                                   1)

  // Signal probe function for `soc_rst_req_async_i` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_rst_req_async,
                                   `TOP_HIER.soc_rst_req_async_i,
                                   1)

  // Signal probe function for `soc_wkup_async_i` of TOP_HIER.
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_soc_wkup_async,
                                   `TOP_HIER.soc_wkup_async_i,
                                   1)

`undef TOP_HIER
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
`undef GPIO_HIER
`undef HMAC_HIER
`undef I2C_HIER
`undef KMAC_HIER
`undef KEYMGR_DPE_HIER
`undef LC_CTRL_HIER
`undef OTBN_HIER
`undef OTP_CTRL_HIER
`undef OTP_MACRO_HIER
`undef PINMUX_HIER
`undef PWRMGR_HIER
`undef ROM_CTRL0_HIER
`undef ROM_CTRL1_HIER
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
`undef UART_HIER

endinterface
