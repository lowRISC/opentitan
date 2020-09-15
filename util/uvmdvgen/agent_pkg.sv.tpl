// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ${name}_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // local types
  // forward declare classes to allow typedefs below
  typedef class ${name}_item;
  typedef class ${name}_agent_cfg;

% if has_separate_host_device_driver:
  // add typedef for ${name}_driver which is dv_base_driver with the right parameter set
  // ${name}_host_driver and ${name}_device_driver will extend from this
  typedef dv_base_driver #(.ITEM_T(${name}_item),
                           .CFG_T (${name}_agent_cfg)) ${name}_driver;

% endif
  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(${name}_item),
                              .CFG_T (${name}_agent_cfg)) ${name}_sequencer;

  // functions

  // package sources
  `include "${name}_item.sv"
  `include "${name}_agent_cfg.sv"
  `include "${name}_agent_cov.sv"
% if has_separate_host_device_driver:
  `include "${name}_host_driver.sv"
  `include "${name}_device_driver.sv"
% else:
  `include "${name}_driver.sv"
% endif
  `include "${name}_monitor.sv"
  `include "${name}_agent.sv"
  `include "${name}_seq_list.sv"

endpackage: ${name}_agent_pkg
