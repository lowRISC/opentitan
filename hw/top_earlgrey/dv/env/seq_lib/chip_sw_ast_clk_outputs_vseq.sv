// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_ast_clk_outputs_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_ast_clk_outputs_vseq)

  `uvm_object_new

  task body();
     // These assertions are invalid with multiple power up / down with
     // frequency measurement, because rise and fall times are
     // severly distorted by clock on / off event.
     $assertoff(0, "tb.dut.top_earlgrey.u_clkmgr_aon.clkmgr_pwrmgr_sva_if.UsbStatusFall_A");
     $assertoff(0, "tb.dut.top_earlgrey.u_clkmgr_aon.clkmgr_pwrmgr_sva_if.UsbStatusRise_A");
     $assertoff(0, "tb.dut.top_earlgrey.u_pwrmgr_aon.clkmgr_pwrmgr_sva_if.UsbStatusFall_A");
     $assertoff(0, "tb.dut.top_earlgrey.u_pwrmgr_aon.clkmgr_pwrmgr_sva_if.UsbStatusRise_A");
     super.body();

  endtask // body

endclass
