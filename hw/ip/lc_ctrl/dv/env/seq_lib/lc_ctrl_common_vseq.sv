// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_common_vseq extends lc_ctrl_base_vseq;
  `uvm_object_utils(lc_ctrl_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    case (if_proxy.sec_cm_type)
      SecCmPrimSparseFsmFlop: begin
        `DV_ASSERT_CTRL_REQ("StateRegs_A", enable)
        `DV_ASSERT_CTRL_REQ("CountRegs_A", enable)
        `DV_ASSERT_CTRL_REQ("FsmStateRegs_A", enable)
        `DV_ASSERT_CTRL_REQ("KmacFsmStateRegs_A", enable)
      end
      SecCmPrimCount: begin
        // No need to disable any assertion
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase
  endfunction : sec_cm_fi_ctrl_svas

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    // Expected state error bit of status register
    bit exp_state_error = 0;
    // Expected lc_state register (actual value is this repeated 6 times)
    // Without error lc_state reflects OTP input
    dec_lc_state_e exp_lc_state_single = dec_lc_state(lc_state_e'(cfg.lc_ctrl_vif.otp_i.state));

    super.check_sec_cm_fi_resp(if_proxy);

    case (if_proxy.sec_cm_type)
      SecCmPrimSparseFsmFlop: begin
        exp_state_error = 1;
        exp_lc_state_single = DecLcStInvalid;
      end

      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase
    csr_rd_check(.ptr(ral.status.state_error), .compare_value(exp_state_error));
    csr_rd_check(.ptr(ral.lc_state), .compare_value({6{exp_lc_state_single}}));

    // Check DUT outputs
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_dft_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_nvm_debug_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_hw_debug_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_cpu_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_creator_seed_sw_rw_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_owner_seed_sw_rw_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_iso_part_sw_rd_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_iso_part_sw_wr_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_seed_hw_rd_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_keymgr_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_escalate_en_o, lc_ctrl_pkg::On)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_check_byp_en_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.clk_byp_req_o, lc_ctrl_pkg::Off)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.flash_rma_req_o, lc_ctrl_pkg::Off)

  endtask : check_sec_cm_fi_resp

endclass
