// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A simple "wrapper" class that holds the virtual interfaces and the configuration knobs needed by
// racl_ctrl_env. This avoids the tb and environment having to do several uvm_config_db
// transactions.

class racl_ctrl_env_wrapper_cfg;
  // The NumSubscribingIps dut parameter
  int unsigned num_subscribing_ips;

  // The NumExternalSubscribingIps dut parameter
  int unsigned num_external_subscribing_ips;

  // An interface bound to the racl_policies_o output port
  virtual racl_ctrl_policies_if policies_vif;

  // An interface bound to the racl_error_i input port
  virtual racl_error_log_if internal_error_vif;

  // An interface bound to the racl_error_external_i input port
  virtual racl_error_log_if external_error_vif;
endclass
