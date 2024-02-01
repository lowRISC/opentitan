// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_kmac_err_chk_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_kmac_err_chk_vseq)

  `uvm_object_new

  task body();
    cfg.m_kmac_agent_cfg.error_rsp_pct = 100;

    wait(cfg.m_kmac_agent_cfg.vif.mon_cb.rsp_done);

    wait_for_fatal_alert(.max_delay(0), .max_wait_cycle(7));

    `DV_CHECK_EQ(cfg.rom_ctrl_vif.pwrmgr_data.done, MuBi4False)
    cfg.m_kmac_agent_cfg.error_rsp_pct = 0;
    dut_init();
  endtask : body

endclass : rom_ctrl_kmac_err_chk_vseq
