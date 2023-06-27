// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_kmac_err_chk_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_kmac_err_chk_vseq)

  `uvm_object_new

  task body();
    bit [$bits(rom_ctrl_pkg::fsm_state_e)-1:0] rdata_state;
    uvm_reg_data_t act_val;

    cfg.m_kmac_agent_cfg.error_rsp_pct = 100;

    wait(cfg.m_kmac_agent_cfg.vif.mon_cb.rsp_done);

    cfg.scoreboard.set_exp_alert("fatal", .is_fatal(1'b1));
    fork
      begin
        ral.fatal_alert_cause.predict(.value('b1), .kind(UVM_PREDICT_READ), .be(4'hF));
        wait_alert_trigger ("fatal", .wait_complete(1));
        csr_utils_pkg::csr_rd(.ptr(ral.fatal_alert_cause), .value(act_val));
      end
      begin
        repeat(3) wait_alert_trigger ("fatal", .wait_complete(1));
      end
    join
    uvm_hdl_read("tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q", rdata_state);
    `DV_CHECK_EQ(rdata_state, rom_ctrl_pkg::Invalid)
    `DV_CHECK_EQ(cfg.rom_ctrl_vif.pwrmgr_data.done, MuBi4False)
    cfg.m_kmac_agent_cfg.error_rsp_pct = 0;
    dut_init();
  endtask : body

endclass : rom_ctrl_kmac_err_chk_vseq
