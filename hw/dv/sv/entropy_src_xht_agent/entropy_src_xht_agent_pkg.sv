// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package entropy_src_xht_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import entropy_src_pkg::*;

  // TODO(#25760): Make the RNG BUS WIDTH parameter overwritable from the outside to allow
  // testing other configs than the Earlgrey config
  parameter uint RNG_BUS_WIDTH = 4;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  `include "entropy_src_xht_item.sv"
  `include "entropy_src_xht_agent_cfg.sv"
  `include "entropy_src_xht_device_driver.sv"
  `include "entropy_src_xht_monitor.sv"
  `include "entropy_src_xht_sequencer.sv"
  `include "entropy_src_xht_seq_list.sv"
  `include "entropy_src_xht_agent.sv"

endpackage : entropy_src_xht_agent_pkg
