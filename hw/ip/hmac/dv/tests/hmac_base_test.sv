// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_base_test extends cip_base_test #(.ENV_T(hmac_env),
                                             .CFG_T(hmac_env_cfg));
  `uvm_component_utils(hmac_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Trigger this feature randomly and could be disabled for some tests
    cfg.save_and_restore_pct = 20;  // In percent chance to happen
  endfunction

endclass : hmac_base_test
