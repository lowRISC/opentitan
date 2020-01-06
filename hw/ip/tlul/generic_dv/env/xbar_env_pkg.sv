// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment package
// ---------------------------------------------
package xbar_env_pkg;

  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;

  typedef struct {
    string                      device_name;
    addr_range_t                addr_ranges[$];
  } tl_device_t;

  typedef struct {
    string                      host_name;
    int                         host_id;
    string                      valid_devices[$];
  } tl_host_t;

  // this file is auto-generated and the path to this file should be provided in xbar_*_sim.core
  `include "xbar_env_pkg__params.sv"

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

  function automatic bit is_device_valid_addr(string device_name, bit [top_pkg::TL_AW-1 : 0] addr);
    foreach (xbar_devices[i]) begin
      if (xbar_devices[i].device_name == device_name) begin
        foreach (xbar_devices[i].addr_ranges[j]) begin
          if (addr inside {[xbar_devices[i].addr_ranges[j].start_addr :
                           xbar_devices[i].addr_ranges[j].end_addr]}) begin
            return 1;
          end
        end
      end
    end
    return 0;
  endfunction

  `include "xbar_env_cfg.sv"
  `include "xbar_env_cov.sv"
  `include "xbar_virtual_sequencer.sv"
  `include "xbar_scoreboard.sv"
  `include "xbar_env.sv"
  `include "xbar_vseq_list.sv"

endpackage
