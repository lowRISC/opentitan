// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_base_test extends cip_base_test #(.ENV_T(hmac_env),
                                             .CFG_T(hmac_env_cfg));
  `uvm_component_utils(hmac_base_test)
  `uvm_component_new

endclass : hmac_base_test
