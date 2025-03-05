// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import chip_env_pkg::*;
  import chip_common_pkg::*;
  import top_pkg::*;
  import top_darjeeling_pkg::*;
  import chip_test_pkg::*;
  import xbar_test_pkg::*;
  import mem_bkdr_util_pkg::*;
  import rom_ctrl_bkdr_util_pkg::*;
  import sram_ctrl_bkdr_util_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "chip_hier_macros.svh"  // TODO: Deprecate this.

  // In most simulations the DV infrastructure provides a virtual interface connected to a
  // concrete clk_rst_if which is completely passive, since the AST provides both.
  // In order to enable cycle waits we connect clk and rst_n to chip internal signals.
  //
  // The XBAR simulation mode uses a different environment, and drives the internal clocks
  // directly, bypassing the AST.
  //
  // XBAR mode uses a different UVM environment than the full chip. It requires the POR to be driven
  // using a clk_rst_if instance. The `xbar_mode` plusarg is used to switch between the two
  // environments. It is declared as type `logic` so that a wait statement can be used in other
  // initial blocks to wait for its value to stabilize after a plusarg lookup.

  // We use two clk_rst_ifs, the passive one for normal full chip tests, and the xbar one for
  // tests running in xbar_mode. The virtual interface clk_rst_vif used by sequences and the
  // infrastructure is selected depending on xbar_mode.

  // The passive clk_rst_if used for full chip testing, and is driven separately with a
  // sensible frequency, just for calls to wait for cycles to be sensible.
  wire passive_clk, passive_rst_n;
  clk_rst_if passive_clk_rst_if(
    .clk(passive_clk),
    .rst_n(passive_rst_n)
  );
  // Reset driver for pad tests.
  assign passive_rst_n = dut.chip_if.dios[top_darjeeling_pkg::DioPadPorN];

  // The interface only drives the clock.
  initial passive_clk_rst_if.set_active(.drive_clk_val(1), .drive_rst_n_val(0));

  // The xbar clk_rst_if is active, but only rst_n is hooked up. It is used in the xbar testbench,
  // so leave it as is.
  wire xbar_clk, rst_n;
  clk_rst_if xbar_clk_rst_if(
    .clk(xbar_clk),
    .rst_n(rst_n)
  );
  initial xbar_clk_rst_if.set_active(.drive_clk_val(1), .drive_rst_n_val(1));

  logic xbar_mode;
  initial begin
    if (!$value$plusargs("xbar_mode=%0b", xbar_mode)) xbar_mode = 0;
    if (xbar_mode)
      uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", xbar_clk_rst_if);
    else
      uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", passive_clk_rst_if);
  end

  assign dut.POR_N = xbar_mode ? rst_n : 1'bz;

  // TODO: Absorb this functionality into chip_if.
  bind dut ast_supply_if ast_supply_if (
    .clk(top_darjeeling.clk_aon_i),
`ifdef GATE_LEVEL
    .core_sleeping_trigger(0),
    .low_power_trigger(0)
`else
    .core_sleeping_trigger(top_darjeeling.rv_core_ibex_pwrmgr.core_sleeping),
    .low_power_trigger(`PWRMGR_HIER.pwr_rst_o.reset_cause == pwrmgr_pkg::LowPwrEntry)
`endif
  );

  // TODO: Absorb this functionality into chip_if.
  bind dut ast_ext_clk_if ast_ext_clk_if ();

  // TODO: Absorb this functionality into chip_if.
  alert_esc_if alert_if[NUM_ALERTS](.clk  (`ALERT_HANDLER_HIER.clk_i),
                                    .rst_n(`ALERT_HANDLER_HIER.rst_ni));
  for (genvar i = 0; i < NUM_ALERTS; i++) begin : gen_connect_alert_rx
    assign alert_if[i].alert_rx = `ALERT_HANDLER_HIER.alert_rx_o[i];
  end

  bind chip_darjeeling_asic chip_if chip_if();

`ifdef DISABLE_ROM_INTEGRITY_CHECK
  chip_darjeeling_asic #(
    // This is to be used carefully, and should never be on for synthesis.
    // It causes many rom features to be disabled, including the very slow
    // integrity check, so full chip simulation runs don't do it for each
    // reset.
    .SecRomCtrl0DisableScrambling(1'b1),
    .SecRomCtrl1DisableScrambling(1'b1)
) dut (
`else
  chip_darjeeling_asic dut (
`endif
    // Dedicated Pads
    .POR_N(dut.chip_if.dios[top_darjeeling_pkg::DioPadPorN]),
    .JTAG_TCK(dut.chip_if.dios[top_darjeeling_pkg::DioPadJtagTck]),
    .JTAG_TMS(dut.chip_if.dios[top_darjeeling_pkg::DioPadJtagTms]),
    .JTAG_TDI(dut.chip_if.dios[top_darjeeling_pkg::DioPadJtagTdi]),
    .JTAG_TDO(dut.chip_if.dios[top_darjeeling_pkg::DioPadJtagTdo]),
    .JTAG_TRST_N(dut.chip_if.dios[top_darjeeling_pkg::DioPadJtagTrstN]),
    .OTP_EXT_VOLT(dut.chip_if.dios[top_darjeeling_pkg::DioPadOtpExtVolt]),
    .SPI_HOST_D0(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiHostD0]),
    .SPI_HOST_D1(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiHostD1]),
    .SPI_HOST_D2(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiHostD2]),
    .SPI_HOST_D3(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiHostD3]),
    .SPI_HOST_CLK(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiHostClk]),
    .SPI_HOST_CS_L(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiHostCsL]),
    .SPI_DEV_D0(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiDevD0]),
    .SPI_DEV_D1(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiDevD1]),
    .SPI_DEV_D2(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiDevD2]),
    .SPI_DEV_D3(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiDevD3]),
    .SPI_DEV_CLK(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiDevClk]),
    .SPI_DEV_CS_L(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiDevCsL]),
    .SPI_DEV_TPM_CS_L(dut.chip_if.dios[top_darjeeling_pkg::DioPadSpiDevTpmCsL]),
    .UART_RX(dut.chip_if.dios[top_darjeeling_pkg::DioPadUartRx]),
    .UART_TX(dut.chip_if.dios[top_darjeeling_pkg::DioPadUartTx]),
    .I2C_SCL(dut.chip_if.dios[top_darjeeling_pkg::DioPadI2cScl]),
    .I2C_SDA(dut.chip_if.dios[top_darjeeling_pkg::DioPadI2cSda]),
    .GPIO0(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio0]),
    .GPIO1(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio1]),
    .GPIO2(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio2]),
    .GPIO3(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio3]),
    .GPIO4(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio4]),
    .GPIO5(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio5]),
    .GPIO6(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio6]),
    .GPIO7(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio7]),
    .GPIO8(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio8]),
    .GPIO9(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio9]),
    .GPIO10(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio10]),
    .GPIO11(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio11]),
    .GPIO12(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio12]),
    .GPIO13(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio13]),
    .GPIO14(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio14]),
    .GPIO15(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio15]),
    .GPIO16(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio16]),
    .GPIO17(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio17]),
    .GPIO18(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio18]),
    .GPIO19(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio19]),
    .GPIO20(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio20]),
    .GPIO21(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio21]),
    .GPIO22(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio22]),
    .GPIO23(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio23]),
    .GPIO24(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio24]),
    .GPIO25(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio25]),
    .GPIO26(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio26]),
    .GPIO27(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio27]),
    .GPIO28(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio28]),
    .GPIO29(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio29]),
    .GPIO30(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio30]),
    .GPIO31(dut.chip_if.dios[top_darjeeling_pkg::DioPadGpio31]),
    .SOC_GPI0(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi0]),
    .SOC_GPI1(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi1]),
    .SOC_GPI2(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi2]),
    .SOC_GPI3(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi3]),
    .SOC_GPI4(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi4]),
    .SOC_GPI5(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi5]),
    .SOC_GPI6(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi6]),
    .SOC_GPI7(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi7]),
    .SOC_GPI8(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi8]),
    .SOC_GPI9(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi9]),
    .SOC_GPI10(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi10]),
    .SOC_GPI11(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpi11]),
    .SOC_GPO0(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo0]),
    .SOC_GPO1(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo1]),
    .SOC_GPO2(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo2]),
    .SOC_GPO3(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo3]),
    .SOC_GPO4(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo4]),
    .SOC_GPO5(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo5]),
    .SOC_GPO6(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo6]),
    .SOC_GPO7(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo7]),
    .SOC_GPO8(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo8]),
    .SOC_GPO9(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo9]),
    .SOC_GPO10(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo10]),
    .SOC_GPO11(dut.chip_if.dios[top_darjeeling_pkg::DioPadSocGpo11]),
    // Muxed Pads
    .MIO0(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio0]),
    .MIO1(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio1]),
    .MIO2(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio2]),
    .MIO3(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio3]),
    .MIO4(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio4]),
    .MIO5(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio5]),
    .MIO6(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio6]),
    .MIO7(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio7]),
    .MIO8(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio8]),
    .MIO9(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio9]),
    .MIO10(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio10]),
    .MIO11(dut.chip_if.mios[top_darjeeling_pkg::MioPadMio11])
  );

  `define SIM_SRAM_IF u_sim_sram.u_sim_sram_if

  // Instantiate & connect the simulation SRAM inside the CPU (rv_core_ibex) using forces.
  bit en_sim_sram = 1'b1;
  wire sel_sim_sram = !dut.chip_if.stub_cpu & en_sim_sram;
`ifdef GATE_LEVEL
  localparam int gsim_TlH2DWidth = $bits(tlul_pkg::tl_h2d_t);
  localparam int gsim_TlD2HWidth = $bits(tlul_pkg::tl_d2h_t);

  logic [gsim_TlH2DWidth-1:0] gsim_tl_win_h2d_int;
  logic [gsim_TlD2HWidth-1:0] gsim_tl_win_d2h_int;

  prim_buf #(
    .Width(gsim_TlH2DWidth)
  ) u_tlul_req_buf (
    .in_i(tlul_pkg::tl_h2d_t'(`CPU_HIER.u_tlul_req_buf.in_i)),
    .out_o(gsim_tl_win_h2d_int)
  );
  prim_buf #(
    .Width(gsim_TlD2HWidth)
  ) u_tlul_rsp_buf (
    .in_i(u_sim_sram.tl_in_o),
    .out_o(gsim_tl_win_d2h_int)
  );
`endif

  sim_sram u_sim_sram (
`ifdef GATE_LEVEL
    .clk_i (sel_sim_sram ?`CPU_HIER.u_core.u_ibex_core.load_store_unit_i.ls_fsm_cs_reg_0_.CK:1'b0),
`else
    .clk_i    (sel_sim_sram ? `CPU_HIER.clk_i : 1'b0),
`endif
    .rst_ni   (`CPU_HIER.rst_ni),
`ifdef GATE_LEVEL
    .tl_in_i  (tlul_pkg::tl_h2d_t'(gsim_tl_win_h2d_int)),
`else
    .tl_in_i  (tlul_pkg::tl_h2d_t'(`CPU_HIER.u_tlul_req_buf.out_o)),
`endif
    .tl_in_o  (),
    .tl_out_o (),
    .tl_out_i ()
  );

  initial begin
    void'($value$plusargs("en_sim_sram=%0b", en_sim_sram));
    if (!dut.chip_if.stub_cpu && en_sim_sram) begin
      `SIM_SRAM_IF.start_addr = SW_DV_START_ADDR;
`ifdef GATE_LEVEL
       force `CPU_HIER.u_tlul_rsp_buf.out_o = gsim_tl_win_d2h_int;
`else
      force `CPU_HIER.u_tlul_rsp_buf.in_i = u_sim_sram.tl_in_o;
`endif
    end
  end

  // Bind the SW test status interface directly to the sim SRAM interface.
  bind `SIM_SRAM_IF sw_test_status_if u_sw_test_status_if (
    .addr     (tl_h2d.a_address),
    .data     (tl_h2d.a_data[15:0]),
    .fetch_en (dut.chip_if.pwrmgr_cpu_fetch_en),
    .*
  );

  // Bind the SW logger interface directly to the sim SRAM interface.
  bind `SIM_SRAM_IF sw_logger_if u_sw_logger_if (
    .addr (tl_h2d.a_address),
    .data (tl_h2d.a_data),
    .*
  );

  initial begin
    // IO Interfaces
    uvm_config_db#(virtual chip_if)::set(null, "*.env", "chip_vif", dut.chip_if);

    // SW logger and test status interfaces.
    uvm_config_db#(virtual sw_test_status_if)::set(
        null, "*.env", "sw_test_status_vif", `SIM_SRAM_IF.u_sw_test_status_if);
    uvm_config_db#(virtual sw_logger_if)::set(
        null, "*.env", "sw_logger_vif", `SIM_SRAM_IF.u_sw_logger_if);

    // AST supply interface.
    uvm_config_db#(virtual ast_supply_if)::set(
        null, "*.env", "ast_supply_vif", dut.ast_supply_if);

    // AST io clk blocker interface.
    uvm_config_db#(virtual ast_ext_clk_if)::set(
        null, "*.env", "ast_ext_clk_vif", dut.ast_ext_clk_if);

    // DMI clk_rst_vif
    uvm_config_db#(virtual clk_rst_if)::set(
        null, "*.env", "clk_rst_vif_chip_soc_dbg_reg_block", dut.chip_if.dmi_clk_rst_if);

    // soc_mbx clk_rst_vif
    uvm_config_db#(virtual clk_rst_if)::set(
        null, "*.env", "clk_rst_vif_chip_soc_mbx_reg_block", dut.chip_if.sys_clk_rst_if);

    // Format time in microseconds losing no precision. The added "." makes it easier to determine
    // the order of magnitude without counting digits, as is needed if it was formatted as ps or ns.
    $timeformat(-6, 6, " us", 13);
    run_test();
  end

  for (genvar i = 0; i < NUM_ALERTS; i++) begin : gen_alert_vif
    initial begin
      uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.m_alert_agent_%0s",
          LIST_OF_ALERTS[i]), "vif", alert_if[i]);
    end
  end

  `undef SIM_SRAM_IF

  // Instantitate the memory backdoor util instances.
  if (`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin : gen_generic
    initial begin
      sram_ctrl_bkdr_util ram_main0, ram_ret0, ram_mbox0;
      // TODO: CTN RAM is NOT actually a scrambled RAM presently. sw_symbol_backdoor_access
      // must be able to modify it.
      sram_ctrl_bkdr_util ram_ctn0;
      rom_ctrl_bkdr_util rom0, rom1;
      chip_mem_e    mem;
      mem_bkdr_util m_mem_bkdr_util[chip_mem_e];

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for I cache way 0 tag", UVM_MEDIUM)
      m_mem_bkdr_util[ICacheWay0Tag] = new(
          .name  ("mem_bkdr_util[ICacheWay0Tag]"),
          .path  (`DV_STRINGIFY(`ICACHE0_TAG_MEM_HIER)),
          .depth ($size(`ICACHE0_TAG_MEM_HIER)),
          .n_bits($bits(`ICACHE0_TAG_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_28_22));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[ICacheWay0Tag], `ICACHE0_TAG_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for I cache way 1 tag", UVM_MEDIUM)
      m_mem_bkdr_util[ICacheWay1Tag] = new(
          .name  ("mem_bkdr_util[ICacheWay1Tag]"),
          .path  (`DV_STRINGIFY(`ICACHE1_TAG_MEM_HIER)),
          .depth ($size(`ICACHE1_TAG_MEM_HIER)),
          .n_bits($bits(`ICACHE1_TAG_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_28_22));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[ICacheWay1Tag], `ICACHE1_TAG_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for I cache way 0 data", UVM_MEDIUM)
      m_mem_bkdr_util[ICacheWay0Data] = new(
          .name  ("mem_bkdr_util[ICacheWay0Data]"),
          .path  (`DV_STRINGIFY(`ICACHE0_DATA_MEM_HIER)),
          .depth ($size(`ICACHE0_DATA_MEM_HIER)),
          .n_bits($bits(`ICACHE0_DATA_MEM_HIER)),
          // The line size is 2x 32 bits and ECC is applied separately at the 32-bit word level.
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[ICacheWay0Data], `ICACHE0_DATA_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for I cache way 1 data", UVM_MEDIUM)
      m_mem_bkdr_util[ICacheWay1Data] = new(
          .name  ("mem_bkdr_util[ICacheWay1Data]"),
          .path  (`DV_STRINGIFY(`ICACHE1_DATA_MEM_HIER)),
          .depth ($size(`ICACHE1_DATA_MEM_HIER)),
          .n_bits($bits(`ICACHE1_DATA_MEM_HIER)),
          // The line size is 2x 32 bits and ECC is applied separately at the 32-bit word level.
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[ICacheWay1Data], `ICACHE1_DATA_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for OTP", UVM_MEDIUM)
      m_mem_bkdr_util[Otp] = new(
          .name  ("mem_bkdr_util[Otp]"),
          .path  (`DV_STRINGIFY(`OTP_MEM_HIER)),
          .depth ($size(`OTP_MEM_HIER)),
          .n_bits($bits(`OTP_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_22_16));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[Otp], `OTP_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for RAM", UVM_MEDIUM)
      ram_main0 = new(
          .name  ("mem_bkdr_util[RamMain0]"),
          .path  (`DV_STRINGIFY(`RAM_MAIN_MEM_HIER)),
          .depth ($size(`RAM_MAIN_MEM_HIER)),
          .n_bits($bits(`RAM_MAIN_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
          .system_base_addr    (top_darjeeling_pkg::TOP_DARJEELING_RAM_MAIN_BASE_ADDR));
      m_mem_bkdr_util[RamMain0] = ram_main0;
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamMain0], `RAM_MAIN_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for RAM RET", UVM_MEDIUM)
       ram_ret0 = new(
          .name  ("mem_bkdr_util[RamRet0]"),
          .path  (`DV_STRINGIFY(`RAM_RET_MEM_HIER)),
          .depth ($size(`RAM_RET_MEM_HIER)),
          .n_bits($bits(`RAM_RET_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
          .system_base_addr    (top_darjeeling_pkg::TOP_DARJEELING_RAM_RET_AON_BASE_ADDR));
      m_mem_bkdr_util[RamRet0] = ram_ret0;
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamRet0], `RAM_RET_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for RAM MBOX", UVM_MEDIUM)
      ram_mbox0 = new(
          .name  ("mem_bkdr_util[RamMbox0]"),
          .path  (`DV_STRINGIFY(`RAM_MBOX_MEM_HIER)),
          .depth ($size(`RAM_MBOX_MEM_HIER)),
          .n_bits($bits(`RAM_MBOX_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
          .system_base_addr    (top_darjeeling_pkg::TOP_DARJEELING_RAM_MBOX_BASE_ADDR));
      m_mem_bkdr_util[RamMbox0] = ram_mbox0;
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamMbox0], `RAM_MBOX_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for RAM CTN", UVM_MEDIUM)
      ram_ctn0 = new(
          .name  ("mem_bkdr_util[RamCtn0]"),
          .path  (`DV_STRINGIFY(`RAM_CTN_MEM_HIER)),
          .depth ($size(`RAM_CTN_MEM_HIER)),
          .n_bits($bits(`RAM_CTN_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
          .system_base_addr    (top_darjeeling_pkg::TOP_DARJEELING_RAM_CTN_BASE_ADDR));
      m_mem_bkdr_util[RamCtn0] = ram_ctn0;
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamCtn0], `RAM_CTN_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for ROM0", UVM_MEDIUM)
      rom0 = new(
          .name  ("mem_bkdr_util[Rom0]"),
          .path  (`DV_STRINGIFY(`ROM0_MEM_HIER)),
          .depth ($size(`ROM0_MEM_HIER)),
          .n_bits($bits(`ROM0_MEM_HIER)),
`ifdef DISABLE_ROM_INTEGRITY_CHECK
          .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone),
`else
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
`endif
          .key   (top_darjeeling_rnd_cnst_pkg::RndCnstRomCtrl0ScrKey),
          .nonce (top_darjeeling_rnd_cnst_pkg::RndCnstRomCtrl0ScrNonce),
          .system_base_addr    (top_darjeeling_pkg::TOP_DARJEELING_ROM0_BASE_ADDR));
      m_mem_bkdr_util[Rom0] = rom0;
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[Rom0], `ROM0_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for ROM1", UVM_MEDIUM)
      rom1 = new(
          .name  ("mem_bkdr_util[Rom1]"),
          .path  (`DV_STRINGIFY(`ROM1_MEM_HIER)),
          .depth ($size(`ROM1_MEM_HIER)),
          .n_bits($bits(`ROM1_MEM_HIER)),
`ifdef DISABLE_ROM_INTEGRITY_CHECK
          .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone),
`else
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
`endif
          .key   (top_darjeeling_rnd_cnst_pkg::RndCnstRomCtrl1ScrKey),
          .nonce (top_darjeeling_rnd_cnst_pkg::RndCnstRomCtrl1ScrNonce),
          .system_base_addr    (top_darjeeling_pkg::TOP_DARJEELING_ROM0_BASE_ADDR));
      m_mem_bkdr_util[Rom1] = rom1;
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[Rom1], `ROM1_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for OTBN IMEM", UVM_MEDIUM)
      m_mem_bkdr_util[OtbnImem] = new(.name  ("mem_bkdr_util[OtbnImem]"),
                                      .path  (`DV_STRINGIFY(`OTBN_IMEM_HIER)),
                                      .depth ($size(`OTBN_IMEM_HIER)),
                                      .n_bits($bits(`OTBN_IMEM_HIER)),
                                      .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[OtbnImem], `OTBN_IMEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for OTBN DMEM", UVM_MEDIUM)
      m_mem_bkdr_util[OtbnDmem0] = new(.name  ("mem_bkdr_util[OtbnDmem0]"),
                                       .path  (`DV_STRINGIFY(`OTBN_DMEM_HIER)),
                                       .depth ($size(`OTBN_DMEM_HIER)),
                                       .n_bits($bits(`OTBN_DMEM_HIER)),
                                       .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[OtbnDmem0], `OTBN_DMEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for SPI_DEVICE EGRESS MEM", UVM_MEDIUM)
      m_mem_bkdr_util[SpiDeviceEgressMem] =
        new(.name  ("mem_bkdr_util[SpiDeviceEgressMem]"),
            .path  (`DV_STRINGIFY(`SPI_DEVICE_EGRESS_HIER)),
            .depth ($size(`SPI_DEVICE_EGRESS_HIER)),
            .n_bits($bits(`SPI_DEVICE_EGRESS_HIER)),
            .err_detection_scheme(mem_bkdr_util_pkg::ParityOdd));

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for SPI_DEVICE INGRESS MEM", UVM_MEDIUM)
      m_mem_bkdr_util[SpiDeviceIngressMem] =
        new(.name  ("mem_bkdr_util[SpiDeviceIngressMem]"),
            .path  (`DV_STRINGIFY(`SPI_DEVICE_INGRESS_HIER)),
            .depth ($size(`SPI_DEVICE_INGRESS_HIER)),
            .n_bits($bits(`SPI_DEVICE_INGRESS_HIER)),
            .err_detection_scheme(mem_bkdr_util_pkg::ParityOdd));

      mem = mem.first();
      do begin
        if (mem inside {FlashBank0Data, FlashBank1Data, FlashBank0Info, FlashBank1Info} ||
            mem inside {[RamMain1:RamMain15]} ||
            mem inside {[RamRet1:RamRet15]} ||
            mem inside {[RamMbox1:RamMbox15]} ||
            mem inside {[RamCtn1:RamCtn15]} ||
            mem inside {[OtbnDmem1:OtbnDmem15]}) begin
          mem = mem.next();
          continue;
        end
        uvm_config_db#(mem_bkdr_util)::set(
            null, "*.env", m_mem_bkdr_util[mem].get_name(), m_mem_bkdr_util[mem]);
        mem = mem.next();
      end while (mem != mem.first());
    end
  end : gen_generic

  // Kill "strong" assertion properties in these scopes at the end of simulation.
  //
  // At the end of the simulation, these assertions start (i.e. the antecedent is true) but before
  // the consequent property is satisfied (which happens a few clocks later), the simulation ends
  // via $finish, causing the simulation to report a failure. It is safe to kill these assertions
  // because they have already succeeded several times during the course of the simulation.
  // TODO: Find a more robust way to turn off these assertions at the end of simulation.
  //
  // This does not apply to VCS. Here'e the relevant note from VCS documentation that explains
  // why:
  // In VCS, strong and weak properties are not distinguished in terms of their reporting at the end
  // of simulation. In all cases, if a property evaluation attempt did not complete evaluation, it
  // is reported as unfinished evaluation attempt, and allows you to decide whether it is a failure
  // or a success.
`ifndef VCS
  final begin
    $assertkill(0, prim_reg_cdc);
    $assertkill(0, sha3pad);
  end
`endif

  initial begin
    fork
      // See chip_padctrl_attributes_vseq for more details.
      forever @dut.chip_if.chip_padctrl_attributes_test_sva_disable begin
        if (dut.chip_if.chip_padctrl_attributes_test_sva_disable) begin
          $assertoff(0, dut.top_darjeeling.u_gpio);
          $assertoff(0, dut.top_darjeeling.u_i2c0);
          $assertoff(0, dut.top_darjeeling.u_pinmux_aon);
          $assertoff(0, dut.top_darjeeling.u_spi_device);
          $assertoff(0, dut.top_darjeeling.u_spi_host0);
          $assertoff(0, dut.top_darjeeling.u_uart0);
        end else begin
          $asserton(0, dut.top_darjeeling.u_gpio);
          $asserton(0, dut.top_darjeeling.u_i2c0);
          $asserton(0, dut.top_darjeeling.u_pinmux_aon);
          $asserton(0, dut.top_darjeeling.u_spi_device);
          $asserton(0, dut.top_darjeeling.u_spi_host0);
          $asserton(0, dut.top_darjeeling.u_uart0);
        end
      end
      // See chip_sw_sleep_pin_mio_dio_val_vseq for more details.
      forever @dut.chip_if.chip_sw_sleep_pin_mio_dio_val_sva_disable begin
        if (dut.chip_if.chip_sw_sleep_pin_mio_dio_val_sva_disable) begin
          $assertoff(0, dut.top_darjeeling.u_spi_device);
        end else begin
          $asserton(0, dut.top_darjeeling.u_spi_device);
        end
      end
    join
  end

  // Control assertions in the DUT with UVM resource string "dut_assert_en".
  `DV_ASSERT_CTRL("dut_assert_en", tb.dut)

  `include "../autogen/tb__xbar_connect.sv"
  `include "../autogen/tb__alert_handler_connect.sv"

  // Gatesim initial
  `ifdef GATE_LEVEL
     initial begin
       // unconnected ports
       force tb.dut.u_ast.u_entropy.dev1_entropy_o = 'h0;
       tb.dut.chip_if.disable_mios_x_check = 1'b1;

       // Ignore 0 time x
       $assertoff();
       #5ns;
       $asserton();
     end
  `endif
endmodule
