// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_ecc_driver
  extends dv_base_driver #(.ITEM_T (ibex_icache_ecc_item),
                           .CFG_T  (ibex_icache_ecc_agent_cfg));

  `uvm_component_utils(ibex_icache_ecc_driver)
  `uvm_component_new

  virtual task reset_signals();
    cfg.vif.reset();
  endtask

  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      cfg.vif.wait_reads(req.delay);
      if (req.two_bits) begin
        cfg.vif.corrupt_read_1(req.bit_pos0);
      end else begin
        cfg.vif.corrupt_read_2(req.bit_pos0, req.bit_pos1);
      end

      seq_item_port.item_done();
    end
  endtask

endclass
