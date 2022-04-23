// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_common_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    super.check_sec_cm_fi_resp(if_proxy);

    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        csr_rd_check(.ptr(ral.fatal_err_code.idle_cnt), .compare_value(1));
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unexpected sec_cm_type %0s", if_proxy.sec_cm_type.name))
      end
    endcase
  endtask

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    if (enable) begin
      $asserton(0, "tb.dut.FpvSecCmClkMainKmacCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainAesCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainHmacCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainOtbnCountCheck_A");
      return;
    end
    if (if_proxy.sec_cm_type == SecCmPrimCount) begin
      $assertoff(0, "tb.dut.FpvSecCmClkMainKmacCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainAesCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainHmacCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainOtbnCountCheck_A");
    end
  endfunction

  task initialize_on_start();
    super.initialize_on_start();
    // update default idle to false for
    // csr test.
    cfg.clkmgr_vif.idle_i = {NUM_TRANS{MuBi4False}};
  endtask : initialize_on_start

endclass
