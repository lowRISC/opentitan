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

  // Finds and returns a sec_cm interface proxy class instance from the sec_cm_if_proxy_q queue.
  //
  // This function matches the first instance whose `path` matches the input argument `path`.
  // A fatal error is thrown if there is no instance in the queue that matches the path.
  // TODO: Allow partial path matching with `uvm_re_match`.
  function automatic sec_cm_base_if_proxy find_sec_cm_if_proxy(string path);
    sec_cm_base_if_proxy proxies[$];
    // Search singleton queue of proxies in sec_cm_pkg
    proxies = sec_cm_pkg::sec_cm_if_proxy_q.find_first() with (item.path == path);
    if (proxies.size > 0) return proxies[0];
    else `uvm_fatal(msg_id, $sformatf("find_sec_cm_if_proxy: no proxy with path %s", path))
  endfunction

endpackage
