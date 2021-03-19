// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_base_test extends cip_base_test #(
    .ENV_T(alert_handler_env),
    .CFG_T(alert_handler_env_cfg)
  );

  `uvm_component_utils(alert_handler_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // alert_handler_env_cfg: cfg
  // alert_handler_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

endclass : alert_handler_base_test

