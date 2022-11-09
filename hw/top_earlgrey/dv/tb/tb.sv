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
  import top_earlgrey_pkg::*;
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
    .POR_N(dut.chip_if.dios[top_earlgrey_pkg::DioPadPorN]),
    .USB_P(dut.chip_if.dios[top_earlgrey_pkg::DioPadUsbP]),
    .USB_N(dut.chip_if.dios[top_earlgrey_pkg::DioPadUsbN]),
    .CC1(dut.chip_if.dios[top_earlgrey_pkg::DioPadCc1]),
    .CC2(dut.chip_if.dios[top_earlgrey_pkg::DioPadCc2]),
    .FLASH_TEST_VOLT(dut.chip_if.dios[top_earlgrey_pkg::DioPadFlashTestVolt]),
    .FLASH_TEST_MODE0(dut.chip_if.dios[top_earlgrey_pkg::DioPadFlashTestMode0]),
    .FLASH_TEST_MODE1(dut.chip_if.dios[top_earlgrey_pkg::DioPadFlashTestMode1]),
    .OTP_EXT_VOLT(dut.chip_if.dios[top_earlgrey_pkg::DioPadOtpExtVolt]),
    .SPI_HOST_D0(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiHostD0]),
    .SPI_HOST_D1(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiHostD1]),
    .SPI_HOST_D2(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiHostD2]),
    .SPI_HOST_D3(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiHostD3]),
    .SPI_HOST_CLK(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiHostClk]),
    .SPI_HOST_CS_L(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiHostCsL]),
    .SPI_DEV_D0(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiDevD0]),
    .SPI_DEV_D1(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiDevD1]),
    .SPI_DEV_D2(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiDevD2]),
    .SPI_DEV_D3(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiDevD3]),
    .SPI_DEV_CLK(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiDevClk]),
    .SPI_DEV_CS_L(dut.chip_if.dios[top_earlgrey_pkg::DioPadSpiDevCsL]),
    .IOR8(dut.chip_if.dios[top_earlgrey_pkg::DioPadIor8]),
    .IOR9(dut.chip_if.dios[top_earlgrey_pkg::DioPadIor9]),
    .AST_MISC(dut.chip_if.ast_misc),

    // Muxed Pads
    .IOA0(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa0]),
    .IOA1(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa1]),
    .IOA2(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa2]),
    .IOA3(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa3]),
    .IOA4(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa4]),
    .IOA5(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa5]),
    .IOA6(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa6]),
    .IOA7(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa7]),
    .IOA8(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoa8]),
    .IOB0(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob0]),
    .IOB1(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob1]),
    .IOB2(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob2]),
    .IOB3(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob3]),
    .IOB4(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob4]),
    .IOB5(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob5]),
    .IOB6(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob6]),
    .IOB7(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob7]),
    .IOB8(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob8]),
    .IOB9(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob9]),
    .IOB10(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob10]),
    .IOB11(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob11]),
    .IOB12(dut.chip_if.mios[top_earlgrey_pkg::MioPadIob12]),
    .IOC0(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc0]),
    .IOC1(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc1]),
    .IOC2(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc2]),
    .IOC3(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc3]),
    .IOC4(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc4]),
    .IOC5(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc5]),
    .IOC6(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc6]),
    .IOC7(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc7]),
    .IOC8(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc8]),
    .IOC9(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc9]),
    .IOC10(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc10]),
    .IOC11(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc11]),
    .IOC12(dut.chip_if.mios[top_earlgrey_pkg::MioPadIoc12]),
    .IOR0(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor0]),
    .IOR1(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor1]),
    .IOR2(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor2]),
    .IOR3(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor3]),
    .IOR4(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor4]),
    .IOR5(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor5]),
    .IOR6(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor6]),
    .IOR7(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor7]),
    .IOR10(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor10]),
    .IOR11(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor11]),
    .IOR12(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor12]),
    .IOR13(dut.chip_if.mios[top_earlgrey_pkg::MioPadIor13])
  );

  `define SIM_SRAM_IF u_sim_sram.u_sim_sram_if

  // Instantiate & connect the simulation SRAM inside the CPU (rv_core_ibex) using forces.
  bit en_sim_sram = 1'b1;
  wire sel_sim_sram = !dut.chip_if.stub_cpu & en_sim_sram;

  sim_sram u_sim_sram (
    .clk_i    (sel_sim_sram ? `CPU_HIER.clk_i : 0),
    .rst_ni   (`CPU_HIER.rst_ni),
    .tl_in_i  (tlul_pkg::tl_h2d_t'(`CPU_HIER.u_tlul_req_buf.out_o)),
    .tl_in_o  (),
    .tl_out_o (),
    .tl_out_i ()
  );

  initial begin
    void'($value$plusargs("en_sim_sram=%0b", en_sim_sram));
    if (!dut.chip_if.stub_cpu && en_sim_sram) begin
      `SIM_SRAM_IF.start_addr = SW_DV_START_ADDR;
      force `CPU_HIER.u_tlul_rsp_buf.in_i = u_sim_sram.tl_in_o;
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
      `MEM_BKDR_UTIL_FILE_OP(m_mem_bkdr_util[FlashBank1Data], `FLASH1_DATA_MEM_HIER)

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

  initial begin
    fork
      // See chip_padctrl_attributes_vseq for more details.
      forever @dut.chip_if.chip_padctrl_attributes_test_sva_disable begin
        if (dut.chip_if.chip_padctrl_attributes_test_sva_disable) begin
          $assertoff(0, dut.top_earlgrey.u_pinmux_aon);
          $assertoff(0, dut.top_earlgrey.u_spi_device);
          $assertoff(0, dut.top_earlgrey.u_spi_host0);
          $assertoff(0, dut.top_earlgrey.u_sysrst_ctrl_aon);
          $assertoff(0, dut.top_earlgrey.u_usbdev);
        end else begin
          $asserton(0, dut.top_earlgrey.u_pinmux_aon);
          $asserton(0, dut.top_earlgrey.u_spi_device);
          $asserton(0, dut.top_earlgrey.u_spi_host0);
          $asserton(0, dut.top_earlgrey.u_sysrst_ctrl_aon);
          $asserton(0, dut.top_earlgrey.u_usbdev);
        end
      end
      // See chip_sw_sleep_pin_mio_dio_val_vseq for more details.
      forever @dut.chip_if.chip_sw_sleep_pin_mio_dio_val_sva_disable begin
        if (dut.chip_if.chip_sw_sleep_pin_mio_dio_val_sva_disable) begin
          $assertoff(0, dut.top_earlgrey.u_spi_device);
        end else begin
          $asserton(0, dut.top_earlgrey.u_spi_device);
        end
      end
    join
  end

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
  assign rst_n = xbar_mode ? 1'bz : dut.chip_if.dios[top_earlgrey_pkg::DioPadPorN];

  `include "../autogen/tb__xbar_connect.sv"
  `include "../autogen/tb__alert_handler_connect.sv"

endmodule
