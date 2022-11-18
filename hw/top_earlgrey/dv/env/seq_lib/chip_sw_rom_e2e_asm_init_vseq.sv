// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_asm_init_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_asm_init_vseq)
  `uvm_object_new

  localparam bit [2:0] EPMP_ACCESS_NONE = 3'b000; // No access.
  localparam bit [2:0] EPMP_ACCESS_RO   = 3'b001; // Read-only access.
  localparam bit [2:0] EPMP_ACCESS_RW   = 3'b011; // Read-write access.
  localparam bit [2:0] EPMP_ACCESS_RX   = 3'b101; // Read-execute access.
  localparam bit [2:0] EPMP_ACCESS_RWX  = 3'b111; // Read-write-execute access.

  localparam bit [31:0] RAM_STACK_GUARD_ADDRESS  = 32'h1001C000;
  localparam bit [31:0] FLASH_TEXT_START_ADDRESS = 32'h20000400;
  localparam bit [31:0] MMIO_START_ADDRESS       = 32'h40000000;
  localparam bit [31:0] MMIO_END_ADDRESS         = 32'h50000000;

  function logic [31:0] epmp_addr_napot(logic [31:0] addr, int unsigned length);
    return ((addr + (length >> 1) - 1) >> 2);
  endfunction

  function logic [31:0] epmp_addr_tor(logic [31:0] addr);
    return (addr >> 2);
  endfunction

  virtual task body();
    lc_ctrl_state_pkg::lc_state_e lc_state = cfg.mem_bkdr_util_h[Otp].otp_read_lc_partition_state();
    bit [31:0] otp_creator_sw_cfg_ast_init_en = 32'b0;
    bit [31:0] otp_creator_sw_cfg_jitter_en = 32'b0;

    super.body();

    // We backdoor read the LC state, AST init enablement state, and clock jitter enablement state
    // from OTP to alter the expectations this test checks below.
    otp_creator_sw_cfg_ast_init_en =
      cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorSwCfgAstInitEnOffset);
    otp_creator_sw_cfg_jitter_en =
      cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorSwCfgJitterEnOffset);

    // Once the retention SRAM is initialized, we have made it to `rom_main()`. At this point, we
    // can start checking CSR states that were configured in the `rom_start.S` assembly.
    `DV_WAIT(cfg.chip_vif.sram_ret_init_done == 1)

    `uvm_info(`gfn, "Checking ROM AST configuration ...", UVM_LOW)
    if (otp_creator_sw_cfg_ast_init_en == prim_mubi_pkg::MuBi4True) begin
      csr_rd_check(.ptr(ral.sensor_ctrl.status.ast_init_done),
                   .compare_value(1),
                   .backdoor(1));
    end else if (otp_creator_sw_cfg_ast_init_en == prim_mubi_pkg::MuBi4False) begin
      csr_rd_check(.ptr(ral.sensor_ctrl.status.ast_init_done),
                   .compare_value(0),
                   .backdoor(1));
    end else begin
      `uvm_fatal(`gfn, "OTP AST init enablement configuration state must be a valid 4-bit MuBi.")
    end

    `uvm_info(`gfn, "Checking ROM clock jitter configuration ...", UVM_LOW)
    csr_rd_check(.ptr(ral.clkmgr_aon.jitter_enable),
                 .compare_value(otp_creator_sw_cfg_jitter_en),
                 .backdoor(1));

    `uvm_info(`gfn, "Checking ROM entropy complex configuration ...", UVM_LOW)
    csr_rd_check(.ptr(ral.entropy_src.conf.fips_enable),
                 .compare_value(prim_mubi_pkg::MuBi4False),
                 .backdoor(1));
    csr_rd_check(.ptr(ral.csrng.ctrl.enable),
                 .compare_value(prim_mubi_pkg::MuBi4True),
                 .backdoor(1));
    csr_rd_check(.ptr(ral.edn0.ctrl.edn_enable),
                 .compare_value(prim_mubi_pkg::MuBi4True),
                 .backdoor(1));
    csr_rd_check(.ptr(ral.edn0.ctrl.boot_req_mode),
                 .compare_value(prim_mubi_pkg::MuBi4True),
                 .backdoor(1));
    csr_rd_check(.ptr(ral.edn0.ctrl.auto_req_mode),
                 .compare_value(prim_mubi_pkg::MuBi4False),
                 .backdoor(1));
    csr_rd_check(.ptr(ral.edn0.ctrl.cmd_fifo_rst),
                 .compare_value(prim_mubi_pkg::MuBi4False),
                 .backdoor(1));

    `uvm_info(`gfn, "Checking ROM ePMP configuration ...", UVM_LOW)
    `DV_CHECK_CASE_EQ(cfg.chip_vif.pmp_mseccfg.mml, 0)
    `DV_CHECK_CASE_EQ(cfg.chip_vif.pmp_mseccfg.mmwp, 1)
    `DV_CHECK_CASE_EQ(cfg.chip_vif.pmp_mseccfg.rlb, 1)

    // ePMP regions 0, 3, 6 -- 10, and 12 are unused.
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[0].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[3].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[6].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[7].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[8].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[9].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[10].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[12].mode, ibex_pkg::PMP_MODE_OFF)

    // ePMP regions for ROM
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[1].mode,  ibex_pkg::PMP_MODE_TOR)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[2].mode,  ibex_pkg::PMP_MODE_NAPOT)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[11].mode, ibex_pkg::PMP_MODE_TOR)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[1].lock)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[2].lock)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[11].lock)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[1][2:0], EPMP_ACCESS_RX)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[2][2:0], EPMP_ACCESS_RO)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[11][2:0], EPMP_ACCESS_RW)

    // ePMP regions for RAM
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[14].mode, ibex_pkg::PMP_MODE_NA4)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[15].mode, ibex_pkg::PMP_MODE_NAPOT)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[14].lock)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[15].lock)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[14][2:0], EPMP_ACCESS_NONE)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[15][2:0], EPMP_ACCESS_RW)

    // ePMP regions for Flash
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[4].mode, ibex_pkg::PMP_MODE_OFF)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[5].mode, ibex_pkg::PMP_MODE_NAPOT)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[5].lock)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[5][2:0], EPMP_ACCESS_RO)

    // ePMP regions for Debug (only enabled in non-prod states)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[13].mode, ibex_pkg::PMP_MODE_NAPOT)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[13].lock)
    if (lc_state inside {LcStProd, LcStProdEnd}) begin
      `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[13][2:0], EPMP_ACCESS_NONE)
    end else begin
      `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[13][2:0], EPMP_ACCESS_RWX)
    end

    // ePMP address entries
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[0],
                 epmp_addr_tor(top_earlgrey_pkg::TOP_EARLGREY_ROM_BASE_ADDR))
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[2],
                 epmp_addr_napot(top_earlgrey_pkg::TOP_EARLGREY_ROM_BASE_ADDR,
                                 top_earlgrey_pkg::TOP_EARLGREY_ROM_SIZE_BYTES))
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[5],
                 epmp_addr_napot(top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR,
                                 top_earlgrey_pkg::TOP_EARLGREY_EFLASH_SIZE_BYTES))
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[10], epmp_addr_tor(MMIO_START_ADDRESS))
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[11], epmp_addr_tor(MMIO_END_ADDRESS))
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[13],
                 epmp_addr_napot(top_earlgrey_pkg::TOP_EARLGREY_RV_DM_MEM_BASE_ADDR,
                                 top_earlgrey_pkg::TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES))
    // PMP NA4 address calculation is the same as the TOR calculation.
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[14], epmp_addr_tor(RAM_STACK_GUARD_ADDRESS))
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[15],
                 epmp_addr_napot(top_earlgrey_pkg::TOP_EARLGREY_RAM_MAIN_BASE_ADDR,
                                 top_earlgrey_pkg::TOP_EARLGREY_RAM_MAIN_SIZE_BYTES))

    // Check interrupts.
    `DV_CHECK_EQ(cfg.chip_vif.mstatus_mie, 0)

    // Check SRAM status.
    csr_rd_check(.ptr(ral.sram_ctrl_main_regs.status.init_done),
                 .compare_value(1),
                 .backdoor(1));
    csr_rd_check(.ptr(ral.sram_ctrl_main_regs.status.scr_key_valid),
                 .compare_value(1),
                 .backdoor(1));
    if (lc_state inside {LcStDev, LcStProd, LcStProdEnd, LcStRma}) begin
      csr_rd_check(.ptr(ral.sram_ctrl_main_regs.status.scr_key_seed_valid),
                   .compare_value(1),
                   .backdoor(1));
    end

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest,
      "Timeout waiting to boot flash stage.", 200_000_000)

    // ePMP is unlocked for flash once the signature verification succeeds.
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[4].mode, ibex_pkg::PMP_MODE_TOR)
    `DV_CHECK(cfg.chip_vif.pmp_cfg[4].lock)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_cfg[4][2:0], EPMP_ACCESS_RX)
    `DV_CHECK_EQ(cfg.chip_vif.pmp_addr[3], epmp_addr_tor(FLASH_TEXT_START_ADDRESS))
  endtask

endclass : chip_sw_rom_e2e_asm_init_vseq
