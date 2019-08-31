// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

% if is_cip:
class ${name}_virtual_sequencer extends cip_base_virtual_sequencer #(
% else:
class ${name}_virtual_sequencer extends dv_base_virtual_sequencer #(
% endif
    .CFG_T(${name}_env_cfg),
    .COV_T(${name}_env_cov)
  );
  `uvm_component_utils(${name}_virtual_sequencer)

% for agent in env_agents:
  ${agent}_sequencer ${agent}_sequencer_h;
% endfor

  `uvm_component_new

endclass
