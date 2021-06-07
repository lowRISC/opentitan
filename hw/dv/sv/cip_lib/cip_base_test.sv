// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_test #(type CFG_T = cip_base_env_cfg,
                      type ENV_T = cip_base_env) extends dv_base_test #(CFG_T, ENV_T);
  `uvm_component_param_utils(cip_base_test #(CFG_T, ENV_T))

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // use cip_tl_seq_item to create tl_seq_item with correct integrity values and obtain integrity
    // related functions
    tl_seq_item::type_id::set_type_override(cip_tl_seq_item::get_type());
  endfunction
endclass : cip_base_test

