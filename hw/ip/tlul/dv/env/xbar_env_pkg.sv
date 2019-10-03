// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment package
// ---------------------------------------------
package xbar_env_pkg;

  import uvm_pkg::*;
  import tl_agent_pkg::*;
  import tl_main_pkg::*;

  typedef struct {
    string                      device_name;
    bit [top_pkg::TL_AW-1 : 0]  start_address;
    bit [top_pkg::TL_AW-1 : 0]  end_address;
  } tl_device_t;

  typedef struct {
    string                      host_name;
    int                         host_id;
    string                      valid_devices[$];
  } tl_host_t;

  `include "xbar_params.svh"

  parameter string D_CHAN_QUEUE_NAME   = "D_CHAN_COMMON_QUEUE";

  function automatic int get_host_id(string name);
    foreach (xbar_hosts[i]) begin
      if (xbar_hosts[i].host_name == name) return i;
    end
    return -1;
  endfunction

  function automatic bit is_valid_path(string host_name, string device_name);
    foreach (xbar_hosts[i]) begin
      if (xbar_hosts[i].host_name == host_name) begin
        foreach (xbar_hosts[i].valid_devices[j]) begin
          if (xbar_hosts[i].valid_devices[j] == device_name)
            return 1;
        end
      end
    end
    return 0;
  endfunction

  `include "xbar_vseqr.sv"
  `include "xbar_scoreboard.sv"
  `include "xbar_env_cfg.sv"
  `include "xbar_env.sv"

endpackage
