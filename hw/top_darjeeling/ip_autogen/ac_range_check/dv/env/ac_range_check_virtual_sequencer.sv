// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(ac_range_check_env_cfg),
    .COV_T(ac_range_check_env_cov)
  );
  `uvm_component_utils(ac_range_check_virtual_sequencer)

  tl_sequencer tl_csr_sqr;
  tl_sequencer tl_unfilt_sqr;
  tl_sequencer tl_filt_sqr;

  `uvm_component_new

endclass
