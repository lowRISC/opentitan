// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_common_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    do_edn_init = 1'b0;

    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task check_sec_cm_fi_resp(sec_cm_pkg::sec_cm_base_if_proxy if_proxy);
    if (!uvm_re_match("*.cnt_q*", if_proxy.path)) begin
      csr_rd_check(.ptr(ral.err_code.edn_cntr_err), .compare_value(1'b1));
    end else if (!uvm_re_match("*.u_edn_ack_sm_ep*", if_proxy.path)) begin
      csr_rd_check(.ptr(ral.err_code.edn_ack_sm_err), .compare_value(1'b1));
    end else if (!uvm_re_match("*.u_edn_main_sm*", if_proxy.path)) begin
      csr_rd_check(.ptr(ral.err_code.edn_main_sm_err), .compare_value(1'b1));
    end
    // TODO: check local escalation and check other EDN request will be blocked.
  endtask
endclass
