// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver that consumes rom_ctrl_kmac_rsp_force_item items and passes them to
// rom_ctrl_fsm_if::override_kmac_digest. This, in turn, will pass the request to
// rom_ctrl_fsm_bound_if, which is the real driver.

class rom_ctrl_kmac_rsp_force_driver extends uvm_driver #(rom_ctrl_kmac_rsp_force_item);
  `uvm_component_utils(rom_ctrl_kmac_rsp_force_driver)

  // The interface through which the driver works. Set this before run_phase by calling set_vif.
  local virtual rom_ctrl_fsm_if m_vif;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Set m_vif. This must be called before run_phase.
  extern function void set_vif(virtual rom_ctrl_fsm_if vif);
endclass

function rom_ctrl_kmac_rsp_force_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

task rom_ctrl_kmac_rsp_force_driver::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal("no_vif", "Cannot drive interface: vif is null.")
    return;
  end

  forever begin
    seq_item_port.get_next_item(req);

    fork : isolation_fork begin
      // This flag shows that the process that calls override_kmac_digest has been scheduled, which
      // means that override_kmac_digest_o will have been set before abort_kmac_digest_override can
      // be called.
      //
      // This structure avoids the call to abort_kmac_digest_override running before the override
      // gets started, even if req.get_abort() is true when the item arrives.
      bit overriding;

      fork
        begin
          if (!req.get_abort()) begin
            overriding = 1;
            m_vif.override_kmac_digest(req.m_digest);
            overriding = 0;
          end
        end
        begin
          req.wait_until_abort();
          if (overriding) m_vif.abort_kmac_digest_override();
          wait(0);
        end
      join_any
      disable fork;
    end join

    seq_item_port.item_done();
  end
endtask

function void rom_ctrl_kmac_rsp_force_driver::set_vif(virtual rom_ctrl_fsm_if vif);
  m_vif = vif;
endfunction
