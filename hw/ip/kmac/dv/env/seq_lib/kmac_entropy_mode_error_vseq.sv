// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Trigger ErrIncorrectEntropyMode error by setting incorrect entropy configuration.
// This sequence will check:
// - Kmac error interrupt is set via check_err() task.
// - Kmac output correct err_code.
// - Kmac can finish the operation without hanging.
// - Check error bit in keymgr app interface.
class kmac_entropy_mode_error_vseq extends kmac_edn_timeout_error_vseq;

  `uvm_object_utils(kmac_entropy_mode_error_vseq)
  `uvm_object_new

  constraint kmac_err_type_c {
    if (en_kmac_err) {
      kmac_err_type == kmac_pkg::ErrIncorrectEntropyMode;
    } else {
      kmac_err_type == kmac_pkg::ErrNone;
    }
  }

  // No assertions to disable.
  virtual function void disable_asserts();
  endfunction

  virtual task check_err_code();
    kmac_pkg::err_t kmac_err = '{valid: 1'b1,
                                 code: kmac_pkg::ErrIncorrectEntropyMode,
                                 info: '0};
    csr_rd_check(.ptr(ral.err_code), .compare_value(kmac_err));
  endtask

  virtual task check_keymgr_rsp_nonblocking();
    fork begin
      while (cfg.en_scb == 0 && entropy_fetched == 0) begin
        wait (cfg.m_kmac_app_agent_cfg[AppKeymgr].vif.kmac_data_rsp.done == 1);
        if (cfg.enable_masking && entropy_mode == ErrIncorrectEntropyMode) begin
          if (entropy_fetched == 0) begin
            `DV_CHECK_EQ(cfg.m_kmac_app_agent_cfg[AppKeymgr].vif.kmac_data_rsp.error, 1)
          end
        end
        wait (cfg.m_kmac_app_agent_cfg[AppKeymgr].vif.kmac_data_rsp.done == 0);
      end
    end join_none
  endtask

endclass
