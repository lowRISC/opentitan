// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence waits for a host request from flash_core bank1,
// then force asserts the host_grant error.
// A fatal error is expected, and checked by the c test (flash_escalation_reset_test.c)
class chip_sw_flash_host_gnt_err_inj_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_flash_host_gnt_err_inj_vseq)
  `uvm_object_new

  localparam string FLASH_BANK1_HOST_GNT_PATH =
       "tb.dut.top_earlgrey.u_flash_ctrl.u_eflash.gen_flash_cores[1].u_core.host_req_i";
  localparam string FLASH_BANK1_HOST_GNT_ERR_PATH =
       "tb.dut.top_earlgrey.u_flash_ctrl.u_eflash.gen_flash_cores[1].u_core.muxed_part";

  virtual task body();
    int polling_timeout_ns = 300_000;
    super.body();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_SPINWAIT(polling_host_gnt();,
                 "polling_host_gnt is timed out",
                 polling_timeout_ns)
    `uvm_info(`gfn, "polling is done", UVM_MEDIUM)
    `DV_CHECK(uvm_hdl_force(FLASH_BANK1_HOST_GNT_ERR_PATH, 1))
    // This value picked to be long enough more than one
    // host request to be sure grant error get asserted.
    #2us;
    `DV_CHECK(uvm_hdl_release(FLASH_BANK1_HOST_GNT_ERR_PATH))
  endtask // body

  task polling_host_gnt();
    bit val;
    while (!val) begin
      `DV_CHECK(uvm_hdl_read(FLASH_BANK1_HOST_GNT_PATH, val));
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask // polling_host_gnt
endclass // chip_sw_flash_host_gnt_err_inj_vseq
