// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_driver extends dv_base_driver #(.ITEM_T(csrng_item),
                                            .CFG_T (csrng_agent_cfg));
  `uvm_component_utils(csrng_driver)

  `uvm_component_new

endclass
