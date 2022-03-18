// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_common_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit[TL_DW-1:0] exp;

    super.check_sec_cm_fi_resp(if_proxy);

    `uvm_info(`gfn, $sformatf("JDONDBG: sec_cm_type %s", if_proxy.sec_cm_type.name), UVM_MEDIUM)
  endtask // check_sec_cm_fi_resp
endclass
