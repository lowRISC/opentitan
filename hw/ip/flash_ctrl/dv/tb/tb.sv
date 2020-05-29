// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import flash_ctrl_env_pkg::*;
  import flash_ctrl_test_pkg::*;

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
  wire intr_op_error;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  tl_if eflash_tl_if(.clk(clk), .rst_n(rst_n));

  // dut
  flash_ctrl_wrapper dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      ),

    .flash_ctrl_tl_i      (tl_if.h2d  ),
    .flash_ctrl_tl_o      (tl_if.d2h  ),

    .eflash_tl_i          (eflash_tl_if.h2d),
    .eflash_tl_o          (eflash_tl_if.d2h),

    .intr_prog_empty_o (intr_prog_empty ),
    .intr_prog_lvl_o   (intr_prog_lvl   ),
    .intr_rd_full_o    (intr_rd_full    ),
    .intr_rd_lvl_o     (intr_rd_lvl     ),
    .intr_op_done_o    (intr_op_done    ),
    .intr_op_error_o   (intr_op_error   )
  );

  // bind mem_bkdr_if
  `define FLASH_MEM_HIER(i) \
      dut.u_flash_eflash.gen_flash_banks[``i``].i_core.i_flash.gen_generic.u_impl_generic.u_mem

  generate
    for (genvar i = 0; i < NUM_FLASH_BANKS; i++) begin : mem_bkdr_if_i
      bind `FLASH_MEM_HIER(i) mem_bkdr_if mem_bkdr_if();
      initial begin
        uvm_config_db#(mem_bkdr_vif)::set(null, "*.env", $sformatf("mem_bkdr_vifs[%0d]", i),
                                          `FLASH_MEM_HIER(i).mem_bkdr_if);
      end
    end
  endgenerate

  `undef FLASH_MEM_HIER

  // Connect the interrupts
  assign interrupts[FlashCtrlIntrProgEmpty] = intr_prog_empty;
  assign interrupts[FlashCtrlIntrProgLvl]   = intr_prog_lvl;
  assign interrupts[FlashCtrlIntrRdFull]    = intr_rd_full;
  assign interrupts[FlashCtrlIntrRdLvl]     = intr_rd_lvl;
  assign interrupts[FlashCtrlIntrOpDone]    = intr_op_done;
  assign interrupts[FlashCtrlIntrOpError]   = intr_op_error;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_eflash_tl_agent*", "vif", eflash_tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
