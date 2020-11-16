// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_driver extends dv_base_driver #(.ITEM_T(keymgr_kmac_item),
                                                  .CFG_T (keymgr_kmac_agent_cfg));
  `uvm_component_utils(keymgr_kmac_driver)

  `uvm_component_new

endclass
