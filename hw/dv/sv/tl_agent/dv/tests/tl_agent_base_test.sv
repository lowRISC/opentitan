// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class tl_agent_base_test extends dv_base_test #(.ENV_T(tl_agent_env), .CFG_T(tl_agent_env_cfg));
  `uvm_component_utils(tl_agent_base_test)
  `uvm_component_new

endclass : tl_agent_base_test

