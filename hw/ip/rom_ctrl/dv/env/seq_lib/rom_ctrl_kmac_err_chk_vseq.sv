// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_kmac_err_chk_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_kmac_err_chk_vseq)

  `uvm_object_new

extern task body();

endclass : rom_ctrl_kmac_err_chk_vseq

task rom_ctrl_kmac_err_chk_vseq::body();
  cfg.m_kmac_agent_cfg.error_rsp_pct = 100;
  expect_fatal_alerts = 1'b1;

  // Wait until kmac has sent a result to rom_ctrl. We know it will contain an error, which should
  // be reflected in an alert from rom_ctrl.
  //
  // Since this takes some time to wait for, exit early if we see a reset.
  fork begin : isolation_fork
    fork
      wait(cfg.under_reset);
      begin
        wait(cfg.m_kmac_agent_cfg.vif.mon_cb.rsp_done);
        wait_for_fatal_alert(.max_delay(4), .max_wait_cycle(7));
        `DV_CHECK_EQ(cfg.rom_ctrl_vif.pwrmgr_data.done, MuBi4False)
      end
    join_any
    disable fork;
  end join

  cfg.m_kmac_agent_cfg.error_rsp_pct = 0;
endtask : body
