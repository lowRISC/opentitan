// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This class inherits from the auto-generated RAL, which in turn inherits from dv_base_reg_block.
class aes_reg_block_extended extends aes_reg_block;
  `uvm_object_utils(aes_reg_block_extended)

  function new(string name = "aes_reg_block_extended", int has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction

  virtual function void get_shadowed_regs(ref dv_base_reg shadowed_regs[$]);
    // Start with the default behavior.
    super.get_shadowed_regs(shadowed_regs);

    // Remove the GCM control register from the list of shadow registers if hardware support for
    // GCM is not enabled. In this case, the writes to the register are ignored anyway.
    if (`EN_GCM == 0) begin
      foreach (shadowed_regs[i]) begin
        if (shadowed_regs[i].get_name() == "ctrl_gcm_shadowed") begin
          shadowed_regs.delete(i);
        end
      end
    end
  endfunction
endclass
