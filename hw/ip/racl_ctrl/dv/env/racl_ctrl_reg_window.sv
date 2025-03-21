// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A "window" into a register block for a templated racl_ctrl instance.
class racl_ctrl_reg_window extends uvm_object;
  `uvm_object_utils(racl_ctrl_reg_window)

  // A queue with the registers that hold the different policies. This is ordered by increasing
  // address (which matches the order of the racl_policies_o port on the dut).
  local dv_base_reg policy_regs[$];

  extern function new (string name="");

  // Set the block variable to point at the given register block (which will have been created by
  // templated code)
  extern function void set_reg_block(uvm_reg_block ral);

  // Get the policy registers, writing them into a queue (a bit like uvm_reg_block::get_registers)
  extern function void get_policy_registers (ref dv_base_reg regs[$]);

  // Get the policy with the given index, returning it as a 32-bit value (padded at the top with
  // zeros)
  extern function bit[31:0] get_policy(int unsigned idx);

  // Return true if register is one of the policy registers
  extern function bit is_policy_reg(uvm_reg register);
endclass

function racl_ctrl_reg_window::new (string name="");
  super.new(name);
endfunction

function void racl_ctrl_reg_window::set_reg_block(uvm_reg_block ral);
  uvm_reg regs[$];
  ral.get_registers(regs);

  policy_regs.delete();

  foreach (regs[i]) begin
    int unsigned pfx_len, suff_len;
    string       reg_name = regs[i].get_name();
    string       policy_name;
    dv_base_reg  dv_reg;

    if (!$cast(dv_reg, regs[i]))
      `uvm_fatal(`gfn, $sformatf("regs[%0d] was not a dv_base_reg.", i))

    // Policy registers start with the prefix "policy_". Skip anything that doesn't. (Note that we
    // don't have to check lengths here: if there aren't enough characters, substr() will return "")
    if (reg_name.substr(0, 6) != "policy_") continue;

    // At this point, we could find the name of the policy by chopping off the "policy_" prefix and
    // also any "_shadowed" suffix. But we don't actually have anything else that cares about policy
    // names (and humans can do the transformation themselves), so we just append this register to
    // policy_regs.
    //
    // Because ral.regs is ordered with increasing addresses, this will match the ordering used for
    // racl_policies_o.
    policy_regs.push_back(dv_reg);
  end

  // As a simple check, make sure that we have the same number of policy registers as the
  // NrRaclPolicies parameter defined in top_racl_pkg.
  if (policy_regs.size() != top_racl_pkg::NrRaclPolicies)
    `uvm_fatal(`gfn,
               $sformatf({"Cannot extract policy registers. ",
                          "top_racl_pkg::NrRaclPolicies = %0d but we have %0d policy registers."},
                         top_racl_pkg::NrRaclPolicies,
                         policy_regs.size()))
endfunction

function void racl_ctrl_reg_window::get_policy_registers (ref dv_base_reg regs[$]);
  foreach (policy_regs[i]) regs.push_back(policy_regs[i]);
endfunction

function bit[31:0] racl_ctrl_reg_window::get_policy(int unsigned idx);
  if (idx >= policy_regs.size()) begin
    `uvm_error(`gfn, $sformatf("Invalid policy index (%0d >= %0d)", idx, policy_regs.size()))
    return 0;
  end
  return policy_regs[idx].get_mirrored_value();
endfunction

function bit racl_ctrl_reg_window::is_policy_reg(uvm_reg register);
  foreach (policy_regs[i]) begin
    if (register == policy_regs[i]) return 1;
  end
  return 0;
endfunction
