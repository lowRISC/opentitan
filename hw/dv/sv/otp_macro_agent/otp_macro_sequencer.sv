// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_macro_sequencer extends dv_base_sequencer #(
  .ITEM_T (otp_macro_item),
  .CFG_T  (otp_macro_agent_cfg)
);
  `uvm_component_utils(otp_macro_sequencer)
  `uvm_component_new
endclass : otp_macro_sequencer
