// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package scoreboard_pkg;

  import uvm_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;

  typedef enum bit {
    kSrcPort = 1'b0,
    kDstPort
  } port_dir_e;

  typedef enum bit [1:0] {
    kInOrderCheck = 2'b0,
    kOutOfOrderCheck,
    kCustomCheck
  } checking_policy_e;

  `include "scoreboard_queue.sv"
  `include "scoreboard.sv"

endpackage
