// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence waits for a host request from flash_core bank1,
// then force flash_part to 'info_partition' to assert the host_grant error.
class chip_sw_flash_host_gnt_err_inj_vseq extends chip_sw_fault_base_vseq;
  `uvm_object_utils(chip_sw_flash_host_gnt_err_inj_vseq)
  `uvm_object_new

  function void set_fault_parameters();
    if_path = "tb.dut.top_earlgrey.u_flash_ctrl.u_eflash.gen_flash_cores[1].u_core";
    alert_id = TopEarlgreyAlertIdFlashCtrlFatalErr;
  endfunction

  task wait_event();
    int polling_timeout_ns = 1_000_000;
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_SPINWAIT(wait(cfg.chip_vif.flash_core1_host_req == 1);,
                 "wait for core1_host_req is timed out",
                 polling_timeout_ns)
    `uvm_info(`gfn, "polling is done", UVM_MEDIUM)
  endtask
endclass // chip_sw_flash_host_gnt_err_inj_vseq
