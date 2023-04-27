// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This triggers a TopEarlgreyAlertIdRstmgrAonFatalCnstyFault fault and checks
// the expected behavior. The test strategy is to cause an unexpected child lc
// reset via force, which will cause the reset consistency checkers to fail and
// cause a fatal error.

class chip_sw_rstmgr_cnsty_fault_vseq extends chip_sw_fault_base_vseq;
  `uvm_object_utils(chip_sw_rstmgr_cnsty_fault_vseq)

  `uvm_object_new

  function void set_fault_parameters();
    if_path = "*rstmgr_aon.u_d0_spi_host0*";
    alert_id = TopEarlgreyAlertIdRstmgrAonFatalCnstyFault;
  endfunction
endclass
