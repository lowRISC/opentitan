// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_common_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // drive dft_en pins to access the test_access memory
    cfg.otp_ctrl_vif.drive_lc_dft_en(lc_ctrl_pkg::On);
    // once turn on lc_dft_en regiser, will need some time to update the state register
    // two clock cycles for lc_async mode, one clock cycle for driving dft_en
    cfg.clk_rst_vif.wait_clks(3);
  endtask

  virtual task post_start();
    super.post_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);

    super.check_sec_cm_fi_resp(if_proxy);

    // TODO, check the status CSR
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
      end
      SecCmPrimSparseFsmFlop: begin
      end
      SecCmPrimDoubleLfsr: begin
        bit[TL_DW-1:0] status_val;

        // TODO, this fault leads to other other errors as well, most of bits in status are set 1,
        // confirm with designer to see if that is expected.
        csr_rd(.ptr(ral.status), .value(status_val));
        `DV_CHECK_EQ(status_val[OtpLfsrFsmErrIdx], 1)
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase

    // TODO, after fault occurs, OTP operation may be blocked. If so, check here
  endtask : check_sec_cm_fi_resp

   virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    // TODO, disable all assertons now
    if (!enable) begin
      $assertoff(0, "tb.dut");
    end
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
      end
      SecCmPrimSparseFsmFlop: begin
      end
      SecCmPrimDoubleLfsr: begin
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase
  endfunction: sec_cm_fi_ctrl_svas

endclass
