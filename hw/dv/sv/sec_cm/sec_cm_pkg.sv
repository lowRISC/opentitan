// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sec_cm_pkg;
  // dep packages
  import uvm_pkg::*;
  import prim_alert_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package variables
  string msg_id = "sec_cm_pkg";

  typedef enum int {
    SecCmPrimCount,
    SecCmPrimSparseFsmFlop,
    SecCmPrimDoubleLfsr,
    SecCmPrimOnehot
  } sec_cm_type_e;

  `include "sec_cm_base_if_proxy.sv"

  // store all the sec_cm proxy classes
  sec_cm_base_if_proxy sec_cm_if_proxy_q[$];
endpackage
