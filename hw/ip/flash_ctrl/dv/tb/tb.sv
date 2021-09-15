// Copyright lowRISC contributors.
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

  wire clk, rst_n;
  wire devmode;
  wire intr_prog_empty;
  wire intr_prog_lvl;
  wire intr_rd_full;
  wire intr_rd_lvl;
  wire intr_op_done;
  wire intr_err;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  tl_if eflash_tl_if(.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  otp_ctrl_pkg::flash_otp_key_req_t otp_req;
  otp_ctrl_pkg::flash_otp_key_rsp_t otp_rsp;

  always_comb begin
    otp_rsp = otp_ctrl_pkg::FLASH_OTP_KEY_RSP_DEFAULT;
    otp_rsp.data_ack = otp_req.data_req;
    otp_rsp.addr_ack = otp_req.addr_req;
  end

  // dut
  flash_ctrl dut (
    .clk_i      (clk      ),
    .rst_ni     (rst_n    ),
    .clk_otp_i  (clk      ),
    .rst_otp_ni (rst_n    ),

    // various tlul interfaces
    .core_tl_i (tl_if.h2d),
    .core_tl_o (tl_if.d2h),
    .prim_tl_i ('0),
    .prim_tl_o (),
    .mem_tl_i  (eflash_tl_if.h2d),
    .mem_tl_o  (eflash_tl_if.d2h),

    // otp interface
    .otp_i (otp_rsp),
    .otp_o (otp_req),

    // various life cycle decode signals
    .lc_creator_seed_sw_rw_en_i (lc_ctrl_pkg::Off),
    .lc_owner_seed_sw_rw_en_i   (lc_ctrl_pkg::On),
    .lc_iso_part_sw_rd_en_i     (lc_ctrl_pkg::On),
    .lc_iso_part_sw_wr_en_i     (lc_ctrl_pkg::On),
    .lc_seed_hw_rd_en_i         (lc_ctrl_pkg::On),
    .lc_nvm_debug_en_i          (lc_ctrl_pkg::Off),
    .lc_escalate_en_i           (lc_ctrl_pkg::Off),

    // life cycle rma handling
    .rma_req_i  (lc_ctrl_pkg::Off),
    .rma_seed_i ('0),
    .rma_ack_o  (),

    // power manager indication
    .pwrmgr_o (pwrmgr_pkg::PWR_FLASH_DEFAULT),
    .keymgr_o (flash_ctrl_keymgr),

    // flash prim signals
    .flash_power_ready_h_i  (1'b1  ),
    .flash_power_down_h_i   (flash_power_down_h  ),
    .flash_bist_enable_i    (lc_ctrl_pkg::Off),
    .flash_test_mode_a_io   (2'h3),
    .flash_test_voltage_h_io(1'b1),

    // test
    .scanmode_i              ('0),
    .scan_rst_ni             ('0),
    .scan_en_i               ('0),

    // alerts and interrupts
    .intr_prog_empty_o  (intr_prog_empty),
    .intr_prog_lvl_o    (intr_prog_lvl  ),
    .intr_rd_full_o     (intr_rd_full   ),
    .intr_rd_lvl_o      (intr_rd_lvl    ),
    .intr_op_done_o     (intr_op_done   ),
    .intr_corr_err_o    (intr_err       ),
    .alert_rx_i         (alert_rx       ),
    .alert_tx_o         (alert_tx       )
  );

  // -----------------------------------
  // Create edge in flash_power_down_h_i, whenever reset is asserted
  logic init;
  assign flash_power_down_h = (init ? 1'b1 : 1'b0);
  initial begin
    forever begin
      fork
        begin : isolation_fork
          if (rst_n === 1'b1) begin
            // Fork off a thread to deassert init after 5 clocks.
            fork
              begin : deassert_init
                clk_rst_if.wait_clks(5);
                init = 1'b0;
              end : deassert_init
            join_none
          end else begin
            init = (rst_n === 1'b0) ? 1'b1 : 1'bx;
          end

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
  `define FLASH_DATA_MEM_HIER(i)                                                        \
      tb.dut.u_eflash.u_flash.gen_generic.u_impl_generic.gen_prim_flash_banks[i].       \
      u_prim_flash_bank.u_mem.gen_generic.u_impl_generic.mem

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
        mem_bkdr_util m_mem_bkdr_util;
        m_mem_bkdr_util = new(.name  ($sformatf("mem_bkdr_util[%0s][%0d]", part.name(), i)),
                              .path  (`FLASH_DATA_MEM_HIER_STR(i)),
                              .depth ($size(`FLASH_DATA_MEM_HIER(i))),
                              .n_bits($bits(`FLASH_DATA_MEM_HIER(i))),
                              .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone));
        uvm_config_db#(mem_bkdr_util)::set(null, "*.env", m_mem_bkdr_util.get_name(),
                                           m_mem_bkdr_util);
        part = part.next();
      end

      for (genvar j = 0; j < flash_ctrl_pkg::InfoTypes; j++) begin : gen_each_info_type
        initial begin
          mem_bkdr_util m_mem_bkdr_util;
          m_mem_bkdr_util = new(.name  ($sformatf("mem_bkdr_util[%0s][%0d]", part.name(), i)),
                                .path  (`FLASH_INFO_MEM_HIER_STR(i, j)),
                                .depth ($size(`FLASH_INFO_MEM_HIER(i, j))),
                                .n_bits($bits(`FLASH_INFO_MEM_HIER(i, j))),
                                .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone));
          uvm_config_db#(mem_bkdr_util)::set(null, "*.env", m_mem_bkdr_util.get_name(),
                                             m_mem_bkdr_util);
          part = part.next();
        end
      end : gen_each_info_type

    end : gen_each_bank
  end : gen_generic

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
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_flash_ctrl_core_reg_block*", "vif",
                                       tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_eflash_tl_agent*", "vif", eflash_tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
