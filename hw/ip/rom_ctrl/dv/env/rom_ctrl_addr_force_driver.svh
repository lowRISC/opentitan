// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver that connects to a rom_ctrl_fsm_if and drives rom_ctrl_addr_force_item items through it.
// This works by forcing the value of the FSM's internal address counter.

class rom_ctrl_addr_force_driver extends uvm_driver #(rom_ctrl_addr_force_item);
  `uvm_component_utils(rom_ctrl_addr_force_driver)

  // The interface through which the driver works. Set this before run_phase by calling set_vif.
  local virtual rom_ctrl_fsm_if m_vif;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Set m_vif. This must be called before run_phase.
  extern function void set_vif(virtual rom_ctrl_fsm_if vif);
endclass

function rom_ctrl_addr_force_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

task rom_ctrl_addr_force_driver::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal("no_vif", "Cannot drive interface: vif is null.")
    return;
  end

  forever begin
    seq_item_port.get_next_item(req);

    // Wait for either the counter's addr_q signal to match req.m_start_addr (lining the timing up
    // with the negedge of the clock to make things more obvious in the waves) or for a reset to be
    // asserted.
    fork : isolation_fork begin
      fork
        begin
          m_vif.wait_for_addr(req.m_start_addr);
          @(negedge m_vif.clk_i);
        end
        wait (!m_vif.rst_ni);
      join_any
      disable fork;
    end join

    // If reset has not been asserted, try to drive the item by calling force_addr. This works by
    // applying a force to override the addr_q value for a cycle but returns early if reset is
    // asserted (releasing the force either way)
    if (m_vif.rst_ni) begin
      `uvm_info("force_addr",
                $sformatf("Forcing word address in rom_ctrl counter from 0x%0h to 0x%0h.",
                          req.m_start_addr, req.m_desired_addr),
                UVM_HIGH)

      m_vif.force_addr(req.m_desired_addr);
    end

    // Either the address has been forced or there has been a reset. Mark the item done either way.
    seq_item_port.item_done();
  end
endtask

function void rom_ctrl_addr_force_driver::set_vif(virtual rom_ctrl_fsm_if vif);
  m_vif = vif;
endfunction
