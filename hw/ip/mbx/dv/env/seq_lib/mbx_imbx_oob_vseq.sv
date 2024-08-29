// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Add extra constraints to the mbx_config to ensure we generate messages
// which exceed the size of the imbx.
// This should trigger a HW-based check when the imbx attempts to write
// outside the configured address range, raising the 'Error' condition.

class mbx_imbx_oob_vseq extends mbx_stress_vseq;

  `uvm_object_utils(mbx_imbx_oob_vseq)
  `uvm_object_new

  function void randomize_mbx_config();
    // Disabling this constraint allows the solver to randomize to an otherwise-invalid
    // config of imbx size + response_dwords that elicits the out-of-bounds error.
    mbx_config.imbx_addr_range_lock_limit_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(mbx_config,
      // imbx_size is inclusive of limit address, hence +1
      ((ibmbx_limit_addr - ibmbx_base_addr) / 4) + 1 < request_dwords;
    )
    `uvm_info(`gfn,
              $sformatf("imbx_size_dwords = %0d, request_dwords = %0d",
                        ((mbx_config.ibmbx_limit_addr - mbx_config.ibmbx_base_addr) / 4) + 1,
                        mbx_config.request_dwords),
              UVM_MEDIUM)
    p_expect_error = 1'b1;
  endfunction

endclass : mbx_imbx_oob_vseq
