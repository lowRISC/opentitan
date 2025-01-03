// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import flash_ctrl_pkg::*;
  import flash_ctrl_env_pkg::*;
  import flash_ctrl_test_pkg::*;
  import mem_bkdr_util_pkg::mem_bkdr_util;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // TB base test ENV_T & CFG_T specification
  //
  // Specify the parameters for the flash_ctrl_base_test
  // This will invoke the UVM registry and link this test type to
  // the name 'flash_ctrl_base_test' as a test name passed by UVM_TESTNAME
  //
  // This is done explicitly only for the prim_pkg::ImplGeneric implementation
  // since partner base tests inherit from flash_ctrl_base_test#(CFG_T, ENV_T) and
  // specify directly (CFG_T, ENV_T) via the class extension and use a different
  // UVM_TESTNAME
  if (`PRIM_DEFAULT_IMPL==prim_pkg::ImplGeneric) begin : gen_spec_base_test_params
    typedef flash_ctrl_base_test #(.CFG_T(flash_ctrl_env_cfg),
                                   .ENV_T(flash_ctrl_env)) flash_ctrl_base_test_t;
  end

  wire clk, rst_n, rst_shadowed_n;
  wire intr_prog_empty;
  wire intr_prog_lvl;
  wire intr_rd_full;
  wire intr_rd_lvl;
  wire intr_op_done;
  wire intr_err;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  rst_shadowed_if rst_shadowed_if (
    .rst_n(rst_n),
    .rst_shadowed_n(rst_shadowed_n)
  );
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  tl_if eflash_tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  tl_if prim_tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  flash_ctrl_if flash_ctrl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  flash_phy_prim_if fpp_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  `define FLASH_DEVICE_HIER tb.dut.u_eflash.u_flash
  assign fpp_if.req = `FLASH_DEVICE_HIER.flash_req_i;
  assign fpp_if.rsp = `FLASH_DEVICE_HIER.flash_rsp_o;
  for (genvar i = 0; i < flash_ctrl_pkg::NumBanks; i++) begin : gen_bank_loop
    assign fpp_if.rreq[i] = tb.dut.u_eflash.gen_flash_cores[i].u_core.u_rd.req_i;
    assign fpp_if.rdy[i] = tb.dut.u_eflash.gen_flash_cores[i].u_core.u_rd.rdy_o;

    assign flash_ctrl_if.hazard[i] =
                        tb.dut.u_eflash.gen_flash_cores[i].u_core.u_rd.data_hazard[3:0];
    assign flash_ctrl_if.evict_prog[i] =
                        tb.dut.u_eflash.gen_flash_cores[i].u_core.u_rd.prog_i;
    assign flash_ctrl_if.evict_erase[i] =
                        tb.dut.u_eflash.gen_flash_cores[i].u_core.u_rd.pg_erase_i;
    for (genvar j = 0; j < flash_phy_pkg::NumBuf; j++) begin : gen_per_buffer
      assign flash_ctrl_if.rd_buf[i][j] =
                        tb.dut.u_eflash.gen_flash_cores[i].u_core.u_rd.read_buf[j];
    end
  end
  assign flash_ctrl_if.fatal_err = tb.dut.fatal_err;
  `undef  FLASH_DEVICE_HIER

  `DV_ALERT_IF_CONNECT()

  // SIMPLE OTP KEY INTERFACE (Access via VIF)

  otp_ctrl_pkg::flash_otp_key_req_t otp_req;
  otp_ctrl_pkg::flash_otp_key_rsp_t otp_rsp;

  assign flash_ctrl_if.otp_req.addr_req = otp_req.addr_req;
  assign flash_ctrl_if.otp_req.data_req = otp_req.data_req;

  assign otp_rsp.addr_ack   = flash_ctrl_if.otp_rsp.addr_ack;
  assign otp_rsp.data_ack   = flash_ctrl_if.otp_rsp.data_ack;
  assign otp_rsp.key        = flash_ctrl_if.otp_rsp.key;
  assign otp_rsp.rand_key   = flash_ctrl_if.otp_rsp.rand_key;
  assign otp_rsp.seed_valid = flash_ctrl_if.otp_rsp.seed_valid;

  assign flash_ctrl_if.rd_buf_en   = tb.dut.u_flash_hw_if.rd_buf_en_o;
  assign flash_ctrl_if.rma_state   = tb.dut.u_flash_hw_if.rma_state_q;
  assign flash_ctrl_if.prog_state0 =
               tb.dut.u_eflash.gen_flash_cores[0].u_core.gen_prog_data.u_prog.state_q;
  assign flash_ctrl_if.prog_state1 =
               tb.dut.u_eflash.gen_flash_cores[1].u_core.gen_prog_data.u_prog.state_q;
  assign flash_ctrl_if.lcmgr_state = tb.dut.u_flash_hw_if.state_q;
  assign flash_ctrl_if.init = tb.dut.u_flash_hw_if.init_i;
  assign flash_ctrl_if.host_gnt = tb.dut.u_eflash.gen_flash_cores[0].u_core.host_gnt;
  assign flash_ctrl_if.ctrl_fsm_idle = tb.dut.u_eflash.gen_flash_cores[0].u_core.ctrl_fsm_idle;
  assign flash_ctrl_if.host_outstanding =
               tb.dut.u_eflash.gen_flash_cores[0].u_core.host_outstanding[1:0];

  assign flash_ctrl_if.hw_rvalid =
               tb.dut.u_flash_hw_if.rvalid_i;

  wire flash_test_v;
  assign (pull1, pull0) flash_test_v = 1'b1;
  wire [1:0] flash_test_mode_a;
  assign (pull1, pull0) flash_test_mode_a = 2'h3;

  // dut
  flash_ctrl #(
    .ProgFifoDepth(ProgFifoDepth),
    .RdFifoDepth(ReadFifoDepth)
  ) dut (
    .clk_i          (clk),
    .rst_ni         (rst_n),
    .rst_shadowed_ni(rst_shadowed_n),
    .clk_otp_i      (clk),
    .rst_otp_ni     (rst_n),

    // various tlul interfaces
    .core_tl_i(tl_if.h2d),
    .core_tl_o(tl_if.d2h),
    .prim_tl_i(prim_tl_if.h2d),
    .prim_tl_o(prim_tl_if.d2h),
    .mem_tl_i (eflash_tl_if.h2d),
    .mem_tl_o (eflash_tl_if.d2h),

    // otp interface
    .otp_i(otp_rsp),
    .otp_o(otp_req),

    // various life cycle decode signals
    .lc_creator_seed_sw_rw_en_i(flash_ctrl_if.lc_creator_seed_sw_rw_en),
    .lc_owner_seed_sw_rw_en_i  (flash_ctrl_if.lc_owner_seed_sw_rw_en),
    .lc_iso_part_sw_rd_en_i    (flash_ctrl_if.lc_iso_part_sw_rd_en),
    .lc_iso_part_sw_wr_en_i    (flash_ctrl_if.lc_iso_part_sw_wr_en),
    .lc_seed_hw_rd_en_i        (flash_ctrl_if.lc_seed_hw_rd_en),
    .lc_nvm_debug_en_i         (flash_ctrl_if.lc_nvm_debug_en),
    .lc_escalate_en_i          (flash_ctrl_if.lc_escalate_en),

    // life cycle rma handling
    .rma_req_i (flash_ctrl_if.rma_req),
    .rma_seed_i(flash_ctrl_if.rma_seed),
    .rma_ack_o (flash_ctrl_if.rma_ack),

    // power manager indication
    .pwrmgr_o(flash_ctrl_if.pwrmgr),
    .keymgr_o(flash_ctrl_if.keymgr),

    // flash prim signals
    .flash_power_ready_h_i  (flash_ctrl_if.power_ready_h),
    .flash_power_down_h_i   (flash_power_down_h),
    .flash_bist_enable_i    (prim_mubi_pkg::MuBi4False),
    .flash_test_mode_a_io   (flash_test_mode_a),
    .flash_test_voltage_h_io(flash_test_v),

    // test
    .scanmode_i (prim_mubi_pkg::MuBi4False),
    .scan_rst_ni('0),
    .scan_en_i  ('0),

    // JTAG
    .cio_tck_i   (flash_ctrl_if.cio_tck),
    .cio_tms_i   (flash_ctrl_if.cio_tms),
    .cio_tdi_i   (flash_ctrl_if.cio_tdi),
    .cio_tdo_en_o(flash_ctrl_if.cio_tdo_en),
    .cio_tdo_o   (flash_ctrl_if.cio_tdo),

    // alerts and interrupts
    .intr_prog_empty_o(intr_prog_empty),
    .intr_prog_lvl_o  (intr_prog_lvl),
    .intr_rd_full_o   (intr_rd_full),
    .intr_rd_lvl_o    (intr_rd_lvl),
    .intr_op_done_o   (intr_op_done),
    .intr_corr_err_o  (intr_err),
    .alert_rx_i       (alert_rx),
    .alert_tx_o       (alert_tx)
  );

  // Create edge in flash_power_down_h_i, whenever reset is asserted
  logic init_pd;
  assign flash_power_down_h = (init_pd ? 1'b1 : 1'b0);
  initial begin
    forever begin
      fork
        begin : isolation_fork
          fork
            begin
              if (rst_n === 1'b1) begin
                // Wait time from reset deassertion to power-down deassertion.
                clk_rst_if.wait_clks(5);
                init_pd = 1'b0;
              end else begin
                // Wait time from reset assertion to power-down assertion. Should match flash-IP
                // spec timing.
                #(flash_ctrl_if.rst_to_pd_time_ns);
                init_pd = 1'b1;
              end
            end
          join_none
          // Wait for the rst_n to change.
          @(rst_n);
          disable fork;
        end : isolation_fork
      join
    end
  end

  // Instantitate the memory backdoor util instances.
  //
  // This only applies to the generic eflash. A unique memory backdoor util instance is created for
  // each type of flash partition in each bank.
  //
  // For eflash of a specific vendor implementation, set the hierarchy to the memory element
  // correctly when creating these instances in the extended testbench.
  `define FLASH_BANK_HIER(i)                                                            \
      tb.dut.u_eflash.u_flash.gen_generic.u_impl_generic.gen_prim_flash_banks[i].       \
      u_prim_flash_bank

  `define FLASH_DATA_MEM_HIER(i)                                                        \
      `FLASH_BANK_HIER(i).u_mem.gen_generic.u_impl_generic.mem

  `define FLASH_DATA_MEM_HIER_STR(i)                                                    \
      $sformatf({"tb.dut.u_eflash.u_flash.gen_generic.u_impl_generic.",                 \
                 "gen_prim_flash_banks[%0d].u_prim_flash_bank.u_mem.gen_generic.",      \
                 "u_impl_generic.mem"}, i)

  `define FLASH_INFO_MEM_HIER(i, j)                                                     \
      tb.dut.u_eflash.u_flash.gen_generic.u_impl_generic.gen_prim_flash_banks[i].       \
      u_prim_flash_bank.gen_info_types[j].u_info_mem.gen_generic.u_impl_generic.mem

  `define FLASH_INFO_MEM_HIER_STR(i, j)                                                 \
      $sformatf({"tb.dut.u_eflash.u_flash.gen_generic.u_impl_generic.",                 \
                 "gen_prim_flash_banks[%0d].u_prim_flash_bank.gen_info_types[%0d].",    \
                 "u_info_mem.gen_generic.u_impl_generic.mem"}, i, j)

  if (`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin : gen_generic
    for (genvar i = 0; i < flash_ctrl_pkg::NumBanks; i++) begin : gen_each_bank
      flash_dv_part_e part = part.first();

      initial begin
        flash_mem_bkdr_util m_mem_bkdr_util;
        m_mem_bkdr_util = new(
            .name($sformatf("mem_bkdr_util[%0s][%0d]", part.name(), i)),
            .path(`FLASH_DATA_MEM_HIER_STR(i)),
            .depth($size(`FLASH_DATA_MEM_HIER(i))),
            .n_bits($bits(`FLASH_DATA_MEM_HIER(i))),
            .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_76_68)
        );
        uvm_config_db#(mem_bkdr_util)::set(null, "*.env", m_mem_bkdr_util.get_name(),
                                           m_mem_bkdr_util);
        part = part.next();
      end

      for (genvar j = 0; j < flash_ctrl_pkg::InfoTypes; j++) begin : gen_each_info_type
        initial begin
          flash_mem_bkdr_util m_mem_bkdr_util;
          m_mem_bkdr_util = new(
              .name($sformatf("mem_bkdr_util[%0s][%0d]", part.name(), i)),
              .path(`FLASH_INFO_MEM_HIER_STR(i, j)),
              .depth($size(`FLASH_INFO_MEM_HIER(i, j))),
              .n_bits($bits(`FLASH_INFO_MEM_HIER(i, j))),
              .err_detection_scheme(mem_bkdr_util_pkg::EccHamming_76_68)
          );
          uvm_config_db#(mem_bkdr_util)::set(null, "*.env", m_mem_bkdr_util.get_name(),
                                             m_mem_bkdr_util);
          part = part.next();
        end
      end : gen_each_info_type

      bind `FLASH_BANK_HIER(i) flash_ctrl_mem_if flash_ctrl_mem_if (
        .clk_i,
        .rst_ni,
        .data_mem_req,
        .mem_wr,
        .mem_addr,
        .mem_wdata,
        .mem_part,
        .mem_info_sel,
        .info0_mem_req (gen_info_types[0].info_mem_req),
        .info1_mem_req (gen_info_types[1].info_mem_req),
        .info2_mem_req (gen_info_types[2].info_mem_req)
      );
      initial begin
        uvm_config_db#(virtual flash_ctrl_mem_if)::set(null, "*.env",
            $sformatf("flash_ctrl_mem_vif[%0d]", i), `FLASH_BANK_HIER(i).flash_ctrl_mem_if);
      end

    end : gen_each_bank
  end : gen_generic

  `undef FLASH_BANK_HIER
  `undef FLASH_DATA_MEM_HIER
  `undef FLASH_INFO_MEM_HIER

  // Connect the interrupts
  assign interrupts[FlashCtrlIntrProgEmpty] = intr_prog_empty;
  assign interrupts[FlashCtrlIntrProgLvl]   = intr_prog_lvl;
  assign interrupts[FlashCtrlIntrRdFull]    = intr_rd_full;
  assign interrupts[FlashCtrlIntrRdLvl]     = intr_rd_lvl;
  assign interrupts[FlashCtrlIntrOpDone]    = intr_op_done;
  assign interrupts[FlashCtrlIntrErr]       = intr_err;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_rst_vif_flash_ctrl_eflash_reg_block", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env",
                                            "clk_rst_vif_flash_ctrl_prim_reg_block", clk_rst_if);

    uvm_config_db#(virtual rst_shadowed_if)::set(null, "*.env", "rst_shadowed_vif",
                                                 rst_shadowed_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_flash_ctrl_core_reg_block*", "vif",
                                       tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_flash_ctrl_eflash_reg_block*", "vif",
                                       eflash_tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_flash_ctrl_prim_reg_block*", "vif",
                                       prim_tl_if);
    uvm_config_db#(virtual flash_ctrl_if)::set(null, "*.env", "flash_ctrl_vif", flash_ctrl_if);
    uvm_config_db#(virtual flash_phy_prim_if)::set(null, "*.env.m_fpp_agent*", "vif", fpp_if);
    $timeformat(-9, 1, " ns", 9);
    run_test();
  end
endmodule
