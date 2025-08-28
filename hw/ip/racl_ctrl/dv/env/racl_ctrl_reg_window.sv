// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A "window" into a register block for a templated racl_ctrl instance.
class racl_ctrl_reg_window extends uvm_object;
  `uvm_object_utils(racl_ctrl_reg_window)

  // A queue with the registers that hold the different policies. This is ordered by increasing
  // address (which matches the order of the racl_policies_o port on the dut).
  local dv_base_reg policy_regs[$];

  // The ERROR_LOG and ERROR_LOG_ADDRESS registers, and the INTR_STATE.RACL_ERROR field.
  local dv_base_reg       error_log_reg;
  local dv_base_reg       error_log_address_reg;
  local dv_base_reg_field racl_error_fld;

  extern function new (string name="");

  // Set the block variable to point at the given register block (which will have been created by
  // templated code)
  extern function void set_reg_block(uvm_reg_block ral);

  // Get the policy registers, writing them into a queue (a bit like uvm_reg_block::get_registers)
  extern function void get_policy_registers (ref dv_base_reg regs[$]);

  // Return true if register is one of the policy registers
  extern function bit is_policy_reg(uvm_reg register);

  // Return the RACL_ERROR field of the INTR_STATE register
  extern function dv_base_reg_field get_intr_state_racl_error_fld();

  // Return the ERROR_LOG register
  extern function dv_base_reg get_error_log_reg();

  // Return the ERROR_LOG_ADDRESS register
  extern function dv_base_reg get_error_log_address_reg();
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

    if (reg_name == "error_log") begin
      error_log_reg = dv_reg;
      continue;
    end
    if (reg_name == "error_log_address") begin
      error_log_address_reg = dv_reg;
      continue;
    end
    if (reg_name == "intr_state") begin
      // There should be a (single) field called racl_error
      racl_error_fld = dv_reg.get_field_by_name("racl_error");
    end

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

  // We should have seen the ERROR_LOG, ERROR_LOG_ADDRESS and INTR_STATE registers
  if (error_log_reg == null) `uvm_fatal(`gfn, "Didn't see an ERROR_LOG register")
  if (error_log_address_reg == null) `uvm_fatal(`gfn, "Didn't see an ERROR_LOG_ADDRESS register")
  if (racl_error_fld == null) `uvm_fatal(`gfn, "Didn't see the INTR_STATE.RACL_ERROR field")
endfunction

function void racl_ctrl_reg_window::get_policy_registers (ref dv_base_reg regs[$]);
  foreach (policy_regs[i]) regs.push_back(policy_regs[i]);
endfunction

function bit racl_ctrl_reg_window::is_policy_reg(uvm_reg register);
  foreach (policy_regs[i]) begin
    if (register == policy_regs[i]) return 1;
  end
  return 0;
endfunction

function dv_base_reg_field racl_ctrl_reg_window::get_intr_state_racl_error_fld();
  return racl_error_fld;
endfunction

function dv_base_reg racl_ctrl_reg_window::get_error_log_reg();
  return error_log_reg;
endfunction

function dv_base_reg racl_ctrl_reg_window::get_error_log_address_reg();
  return error_log_address_reg;
endfunction
