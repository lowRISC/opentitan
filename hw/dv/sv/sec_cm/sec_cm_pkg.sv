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
  // The argument `is_regex` indicates that the `path` is not a full path, but a regular expression.
  function automatic sec_cm_base_if_proxy find_sec_cm_if_proxy(string path, bit is_regex = 0);
    sec_cm_base_if_proxy proxies[$];
    if (is_regex) begin
      proxies = sec_cm_pkg::sec_cm_if_proxy_q.find_first() with (!uvm_re_match(path, item.path));
    end else begin
      proxies = sec_cm_pkg::sec_cm_if_proxy_q.find_first() with (item.path == path);
    end
    if (proxies.size()) begin
      `uvm_info(msg_id, $sformatf({"find_sec_cm_if_proxy: found proxy instance for path %s: ",
                                   "type = %0d, full path = %0s"}, path, proxies[0].sec_cm_type,
                                  proxies[0].path), UVM_MEDIUM)
      return proxies[0];
    end
    else `uvm_fatal(msg_id, $sformatf("find_sec_cm_if_proxy: no proxy with path %s", path))
    return null;
  endfunction

endpackage
