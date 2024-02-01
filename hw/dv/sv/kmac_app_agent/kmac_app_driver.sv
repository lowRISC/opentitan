// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_driver extends dv_base_driver #(.ITEM_T(kmac_app_item),
                                                  .CFG_T (kmac_app_agent_cfg));
  `uvm_component_utils(kmac_app_driver)

  `uvm_component_new

endclass
