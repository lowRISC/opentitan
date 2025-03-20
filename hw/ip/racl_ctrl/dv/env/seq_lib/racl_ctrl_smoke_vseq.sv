// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A smoke test vseq that writes a value for each policy, which will check that policy is getting
// mirrored correctly on the racl_policies_o port.

class racl_ctrl_smoke_vseq extends racl_ctrl_base_vseq;
  `uvm_object_utils(racl_ctrl_smoke_vseq)

  extern function new (string name="");
  extern task body();
endclass

function racl_ctrl_smoke_vseq::new (string name="");
  super.new(name);
endfunction

task racl_ctrl_smoke_vseq::body();
  dv_base_reg regs[$];
  cfg.regs.get_policy_registers(regs);
  repeat (2 * regs.size()) begin
    int unsigned i = $urandom_range(0, regs.size() - 1);
    // Write an arbitrary random value to the register. Not every bit will correspond to a role,
    // because the encoding uses bits 0..n; 16..16+n. But extra bits will be ignored anyway, so it
    // doesn't really matter.
    bit [31:0] val = $urandom;

    // Write val to the register. If the register was shadowed, we'll need to do it twice.
    repeat (regs[i].get_is_shadowed() ? 2 : 1) begin
      uvm_status_e status;
      regs[i].write(status, val);

      // Unless we went into reset, we expect the write to go through
      if (cfg.under_reset) return;
      if (status != UVM_IS_OK)
        `uvm_error(`gfn, $sformatf("Failed to write register %s", regs[i].get_name()))
    end
  end
endtask
