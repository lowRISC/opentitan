// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ICEBOX(#10996): Based on kmac_app sequence, drive partial data by sending `strb` value that is not
// always equal to `8'hFF`.
class kmac_app_with_partial_data_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_app_with_partial_data_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    for (int i = 0; i < kmac_pkg::NumAppIntf; i++) begin
      cfg.m_kmac_app_agent_cfg[i].inject_zero_in_host_strb = 1;
    end
    cfg.do_cycle_accurate_check = 0;
  endtask

endclass
