// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cheriot_base_test extends cip_base_test #(
    .CFG_T(cheriot_env_cfg),
    .ENV_T(cheriot_env)
  );

  `uvm_component_utils(cheriot_base_test)
  `uvm_component_new

endclass : cheriot_base_test
