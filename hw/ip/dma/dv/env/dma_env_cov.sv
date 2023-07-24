// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_env_cov extends cip_base_env_cov #(.CFG_T(dma_env_cfg));
  `uvm_component_utils(dma_env_cov)

  `uvm_component_new
endclass
