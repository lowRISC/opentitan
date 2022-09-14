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
  import chip_common_pkg::*;
  import top_pkg::*;
  import chip_test_pkg::*;
  import xbar_test_pkg::*;
  import mem_bkdr_util_pkg::mem_bkdr_util;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "chip_hier_macros.svh"  // TODO: Deprecate this.

  // interfaces

  // Legacy clk_rst_if to satisfy our CIP base classes. DO NOT USE it in test sequences.
  //
  // This interface has an active clock driver, but the clock port is not connected to anything. The
  // reset port is passive and is connected to the chip's POR_N port. The reset port is active only
  // in `xbar_mode`, because a different UVM environment is in use, which does not have the chip_if.
  // For the regular chip tests, the chip_if is used exclusively to drive all chip's ports.
  //
  // The bogus active clock is made to match the chip's main clock frequency. This is done to
  // ensure compatibility with the CIP / DV lib base sequence classes which assume certain things.
  // This clk_rst_if (which is available in the chip env as cfg.clk_rst_vif) should not be used to
  // wait for clock events. Most tests will not require an external clock source - they will use
  // internally generated clock provided by AST.
  //
  // Note that attempting to drive the external clock / power on reset using this interface will
  // vacuously return instead of throwing an error. This is done to support the our base classes.
  // To do so, the test sequences must use chip_vif.ext_clk_if and chip_vif.por_n_if respectively.
  wire clk, rst_n;
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));

  // TODO: Absorb this functionality into chip_if.
  bind dut ast_supply_if ast_supply_if (
    .clk(top_earlgrey.clk_aon_i),
    .core_sleeping_trigger(top_earlgrey.rv_core_ibex_pwrmgr.core_sleeping),
    .low_power_trigger(`PWRMGR_HIER.pwr_rst_o.reset_cause == pwrmgr_pkg::LowPwrEntry)
  );

  // TODO: Absorb this functionality into chip_if.
  bind dut ast_ext_clk_if ast_ext_clk_if ();

  // TODO: Absorb this functionality into chip_if.
  alert_esc_if alert_if[NUM_ALERTS](.clk  (`ALERT_HANDLER_HIER.clk_i),
                                    .rst_n(`ALERT_HANDLER_HIER.rst_ni));
  for (genvar i = 0; i < NUM_ALERTS; i++) begin : gen_connect_alert_rx
    assign alert_if[i].alert_rx = `ALERT_HANDLER_HIER.alert_rx_o[i];
  end

  bind chip_earlgrey_asic chip_if chip_if();

`ifdef DISABLE_ROM_INTEGRITY_CHECK
  chip_earlgrey_asic #(
    // This is to be used carefully, and should never be on for synthesis.
    // It causes many rom features to be disabled, including the very slow
    // integrity check, so full chip simulation runs don't do it for each
    // reset.
    .SecRomCtrlDisableScrambling(1'b1)
) dut (
`else
  chip_earlgrey_asic dut (
`endif
    // Dedicated Pads
    .POR_N(dut.chip_if.ios[PorN]), // Manual Pad
    .USB_P(dut.chip_if.ios[UsbP]), // Manual Pad
    .USB_N(dut.chip_if.ios[UsbN]), // Manual Pad
    .CC1(dut.chip_if.ios[CC1]), // Manual Pad
    .CC2(dut.chip_if.ios[CC2]), // Manual Pad
    .FLASH_TEST_VOLT(dut.chip_if.ios[FlashTestVolt]), // Manual Pad
    .FLASH_TEST_MODE0(dut.chip_if.ios[FlashTestMode0]), // Manual Pad
    .FLASH_TEST_MODE1(dut.chip_if.ios[FlashTestMode1]), // Manual Pad
    .OTP_EXT_VOLT(dut.chip_if.ios[OtpExtVolt]), // Manual Pad
    .SPI_HOST_D0(dut.chip_if.ios[SpiHostD0]), // Dedicated Pad for spi_host0_sd
    .SPI_HOST_D1(dut.chip_if.ios[SpiHostD1]), // Dedicated Pad for spi_host0_sd
    .SPI_HOST_D2(dut.chip_if.ios[SpiHostD2]), // Dedicated Pad for spi_host0_sd
    .SPI_HOST_D3(dut.chip_if.ios[SpiHostD3]), // Dedicated Pad for spi_host0_sd
    .SPI_HOST_CLK(dut.chip_if.ios[SpiHostClk]), // Dedicated Pad for spi_host0_sck
    .SPI_HOST_CS_L(dut.chip_if.ios[SpiHostCsL]), // Dedicated Pad for spi_host0_csb
    .SPI_DEV_D0(dut.chip_if.ios[SpiDevD0]), // Dedicated Pad for spi_device_sd
    .SPI_DEV_D1(dut.chip_if.ios[SpiDevD1]), // Dedicated Pad for spi_device_sd
    .SPI_DEV_D2(dut.chip_if.ios[SpiDevD2]), // Dedicated Pad for spi_device_sd
    .SPI_DEV_D3(dut.chip_if.ios[SpiDevD3]), // Dedicated Pad for spi_device_sd
    .SPI_DEV_CLK(dut.chip_if.ios[SpiDevClk]), // Dedicated Pad for spi_device_sck
    .SPI_DEV_CS_L(dut.chip_if.ios[SpiDevCsL]), // Dedicated Pad for spi_device_csb
    .IOR8(dut.chip_if.ios[IoR8]), // Dedicated Pad for sysrst_ctrl_aon_ec_rst_l
    .IOR9(dut.chip_if.ios[IoR9]), // Dedicated Pad for sysrst_ctrl_aon_flash_wp_l
    .AST_MISC(dut.chip_if.ios[AstMisc]), // Manual Pad

    // Muxed Pads
    .IOA0(dut.chip_if.ios[IoA0]), // MIO Pad 0
    .IOA1(dut.chip_if.ios[IoA1]), // MIO Pad 1
    .IOA2(dut.chip_if.ios[IoA2]), // MIO Pad 2
    .IOA3(dut.chip_if.ios[IoA3]), // MIO Pad 3
    .IOA4(dut.chip_if.ios[IoA4]), // MIO Pad 4
    .IOA5(dut.chip_if.ios[IoA5]), // MIO Pad 5
    .IOA6(dut.chip_if.ios[IoA6]), // MIO Pad 6
    .IOA7(dut.chip_if.ios[IoA7]), // MIO Pad 7
    .IOA8(dut.chip_if.ios[IoA8]), // MIO Pad 8
    .IOB0(dut.chip_if.ios[IoB0]), // MIO Pad 9
    .IOB1(dut.chip_if.ios[IoB1]), // MIO Pad 10
    .IOB2(dut.chip_if.ios[IoB2]), // MIO Pad 11
    .IOB3(dut.chip_if.ios[IoB3]), // MIO Pad 12
    .IOB4(dut.chip_if.ios[IoB4]), // MIO Pad 13
    .IOB5(dut.chip_if.ios[IoB5]), // MIO Pad 14
    .IOB6(dut.chip_if.ios[IoB6]), // MIO Pad 15
    .IOB7(dut.chip_if.ios[IoB7]), // MIO Pad 16
    .IOB8(dut.chip_if.ios[IoB8]), // MIO Pad 17
    .IOB9(dut.chip_if.ios[IoB9]), // MIO Pad 18
    .IOB10(dut.chip_if.ios[IoB10]), // MIO Pad 19
    .IOB11(dut.chip_if.ios[IoB11]), // MIO Pad 20
    .IOB12(dut.chip_if.ios[IoB12]), // MIO Pad 21
    .IOC0(dut.chip_if.ios[IoC0]), // MIO Pad 22
    .IOC1(dut.chip_if.ios[IoC1]), // MIO Pad 23
    .IOC2(dut.chip_if.ios[IoC2]), // MIO Pad 24
    .IOC3(dut.chip_if.ios[IoC3]), // MIO Pad 25
    .IOC4(dut.chip_if.ios[IoC4]), // MIO Pad 26
    .IOC5(dut.chip_if.ios[IoC5]), // MIO Pad 27
    .IOC6(dut.chip_if.ios[IoC6]), // MIO Pad 28
    .IOC7(dut.chip_if.ios[IoC7]), // MIO Pad 29
    .IOC8(dut.chip_if.ios[IoC8]), // MIO Pad 30
    .IOC9(dut.chip_if.ios[IoC9]), // MIO Pad 31
    .IOC10(dut.chip_if.ios[IoC10]), // MIO Pad 32
    .IOC11(dut.chip_if.ios[IoC11]), // MIO Pad 33
    .IOC12(dut.chip_if.ios[IoC12]), // MIO Pad 34
    .IOR0(dut.chip_if.ios[IoR0]), // MIO Pad 35
    .IOR1(dut.chip_if.ios[IoR1]), // MIO Pad 36
    .IOR2(dut.chip_if.ios[IoR2]), // MIO Pad 37
    .IOR3(dut.chip_if.ios[IoR3]), // MIO Pad 38
    .IOR4(dut.chip_if.ios[IoR4]), // MIO Pad 39
    .IOR5(dut.chip_if.ios[IoR5]), // MIO Pad 40
    .IOR6(dut.chip_if.ios[IoR6]), // MIO Pad 41
    .IOR7(dut.chip_if.ios[IoR7]), // MIO Pad 42
    .IOR10(dut.chip_if.ios[IoR10]), // MIO Pad 43
    .IOR11(dut.chip_if.ios[IoR11]), // MIO Pad 44
    .IOR12(dut.chip_if.ios[IoR12]), // MIO Pad 45
    .IOR13(dut.chip_if.ios[IoR13])  // MIO Pad 46
  );

  `define SIM_SRAM_IF u_sim_sram.u_sim_sram_if

  // Instantiate & connect the simulation SRAM inside the CPU (rv_core_ibex) using forces.
  sim_sram u_sim_sram (
    .clk_i    (`CPU_HIER.clk_i),
    .rst_ni   (`CPU_HIER.rst_ni),
    .tl_in_i  (tlul_pkg::tl_h2d_t'(`CPU_HIER.u_tlul_req_buf.out_o)),
    .tl_in_o  (),
    .tl_out_o (),
    .tl_out_i ()
  );

  bit en_sim_sram = 1'b1;

  initial begin
    void'($value$plusargs("en_sim_sram=%0b", en_sim_sram));
    if (!dut.chip_if.stub_cpu && en_sim_sram) begin
      `SIM_SRAM_IF.start_addr = SW_DV_START_ADDR;
      force `CPU_HIER.u_tlul_rsp_buf.in_i = u_sim_sram.tl_in_o;
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
      chip_mem_e    mem;
      mem_bkdr_util m_mem_bkdr_util[chip_mem_e];

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for flash 0 data", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank0Data] = new(
          .name  ("mem_bkdr_util[FlashBank0Data]"),
          .path  (`DV_STRINGIFY(`FLASH0_DATA_MEM_HIER)),
          .depth ($size(`FLASH0_DATA_MEM_HIER)),
          .n_bits($bits(`FLASH0_DATA_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_76_68),
          .system_base_addr    (top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank0Data], `FLASH0_DATA_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for flash 0 info", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank0Info] = new(
          .name  ("mem_bkdr_util[FlashBank0Info]"),
          .path  (`DV_STRINGIFY(`FLASH0_INFO_MEM_HIER)),
          .depth ($size(`FLASH0_INFO_MEM_HIER)),
          .n_bits($bits(`FLASH0_INFO_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_76_68),
          .system_base_addr    (top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank0Info], `FLASH0_INFO_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for flash 1 data", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank1Data] = new(
          .name  ("mem_bkdr_util[FlashBank1Data]"),
          .path  (`DV_STRINGIFY(`FLASH1_DATA_MEM_HIER)),
          .depth ($size(`FLASH1_DATA_MEM_HIER)),
          .n_bits($bits(`FLASH1_DATA_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_76_68),
          .system_base_addr    (top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR +
              top_earlgrey_pkg::TOP_EARLGREY_EFLASH_SIZE_BYTES / flash_ctrl_pkg::NumBanks));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank1Data], `FLASH0_DATA_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for flash 1 info", UVM_MEDIUM)
      m_mem_bkdr_util[FlashBank1Info] = new(
          .name  ("mem_bkdr_util[FlashBank1Info]"),
          .path  (`DV_STRINGIFY(`FLASH1_INFO_MEM_HIER)),
          .depth ($size(`FLASH1_INFO_MEM_HIER)),
          .n_bits($bits(`FLASH1_INFO_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_76_68),
          .system_base_addr    (top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR +
              top_earlgrey_pkg::TOP_EARLGREY_EFLASH_SIZE_BYTES / flash_ctrl_pkg::NumBanks));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank1Info], `FLASH1_INFO_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for OTP", UVM_MEDIUM)
      m_mem_bkdr_util[Otp] = new(
          .name  ("mem_bkdr_util[Otp]"),
          .path  (`DV_STRINGIFY(`OTP_MEM_HIER)),
          .depth ($size(`OTP_MEM_HIER)),
          .n_bits($bits(`OTP_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_22_16));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[Otp], `OTP_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for RAM", UVM_MEDIUM)
      m_mem_bkdr_util[RamMain0] = new(
          .name  ("mem_bkdr_util[RamMain0]"),
          .path  (`DV_STRINGIFY(`RAM_MAIN_MEM_HIER)),
          .depth ($size(`RAM_MAIN_MEM_HIER)),
          .n_bits($bits(`RAM_MAIN_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
          .system_base_addr    (top_earlgrey_pkg::TOP_EARLGREY_RAM_MAIN_BASE_ADDR));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamMain0], `RAM_MAIN_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for RAM RET", UVM_MEDIUM)
      m_mem_bkdr_util[RamRet0] = new(
          .name  ("mem_bkdr_util[RamRet0]"),
          .path  (`DV_STRINGIFY(`RAM_RET_MEM_HIER)),
          .depth ($size(`RAM_RET_MEM_HIER)),
          .n_bits($bits(`RAM_RET_MEM_HIER)),
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
          .system_base_addr    (top_earlgrey_pkg::TOP_EARLGREY_RAM_RET_AON_BASE_ADDR));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[RamRet0], `RAM_RET_MEM_HIER)

      `uvm_info("tb.sv", "Creating mem_bkdr_util instance for ROM", UVM_MEDIUM)
      m_mem_bkdr_util[Rom] = new(
          .name  ("mem_bkdr_util[Rom]"),
          .path  (`DV_STRINGIFY(`ROM_MEM_HIER)),
          .depth ($size(`ROM_MEM_HIER)),
          .n_bits($bits(`ROM_MEM_HIER)),
`ifdef DISABLE_ROM_INTEGRITY_CHECK
          .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone),
`else
          .err_detection_scheme(mem_bkdr_util_pkg::EccInv_39_32),
`endif
          .system_base_addr    (top_earlgrey_pkg::TOP_EARLGREY_ROM_BASE_ADDR));
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[Rom], `ROM_MEM_HIER)

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

      mem = mem.first();
      do begin
        if (mem inside {[RamMain1:RamMain15]} ||
            mem inside {[RamRet1:RamRet15]} ||
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

  // Control assertions in the DUT with UVM resource string "dut_assert_en".
  `DV_ASSERT_CTRL("dut_assert_en", tb.dut)

  // XBAR mode.
  //
  // XBAR mode uses a different UVM environment than the full chip. It requires the POR to be driven
  // using a clk_rst_if instance. The `xbar_mode` plusarg is used to switch between the two
  // environments. It is declared as type `logic` so that a wait statement can be used in other
  // initial blocks to wait for its value to stabilize after a plusarg lookup.
  logic xbar_mode;

  initial begin
    if (!$value$plusargs("xbar_mode=%0b", xbar_mode)) xbar_mode = 0;
    clk_rst_if.set_active(.drive_clk_val(1 /* bogus clock */), .drive_rst_n_val(xbar_mode));
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", clk_rst_if);
  end
  assign dut.POR_N = xbar_mode ? rst_n : 1'bz;
  assign rst_n = xbar_mode ? 1'bz : dut.chip_if.ios[PorN];

  `include "../autogen/tb__xbar_connect.sv"
  `include "../autogen/tb__alert_handler_connect.sv"

endmodule
