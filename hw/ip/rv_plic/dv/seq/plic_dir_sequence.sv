// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class plic_dir_sequence #(int src=32) extends plic_sequence#(src);

  `uvm_object_utils(plic_dir_sequence)

  irq_seq_item #(src) irq_transaction;

  logic [31:0] base_addr;

  function new(string name = "plic_dir_sequence");
    super.new(name);
  endfunction : new

  task body();
    super.body();
    `uvm_info(get_name(), "Initialization is done", UVM_DEBUG )

    uvm_config_db#(logic [31:0])::get(null,"*","plic_base_address", base_addr);
    // TODO: Wait until irq_agent report interrupt event.
    fork
      irq_service();
      //irq_polling();
    join

    #10us;
  endtask : body

  task irq_polling();
    automatic logic [31:0] rdata, ip, irq_id;
    // Currently, just poll until interrupt received
    do begin
      tl_seq(base_addr, 1'b0, 'h0000_0000, rdata);
      `uvm_info(get_name(), $sformatf("Interrupt Pending: 'h%08x", rdata), UVM_INFO)
      ip = rdata;
      if (ip != 'h0) begin
        // Claim
        tl_seq(base_addr + rv_plic_reg_pkg::RV_PLIC_CC0_OFFSET, 1'b0, 'h0000_0000, rdata);
        irq_id = rdata;
        `uvm_info(get_name(), $sformatf("IRQ Claimed: %d", irq_id ), UVM_INFO)
        if (irq_id == 'h0) begin
          // No interrupt greater than threshold
        end
      end
    end while (irq_id != 'h0);
  endtask : irq_polling

  task irq_service();
    automatic logic [31:0] rdata, ip, irq_id;

    forever begin
      m_irq_fifo.get(irq_transaction);
      irq_transaction.print();

      // Claim
      tl_seq(base_addr + rv_plic_reg_pkg::RV_PLIC_CC0_OFFSET, 1'b0, 'h0000_0000, rdata);
      irq_id = rdata;
      `uvm_info(get_name(), $sformatf("IRQ Claimed: %d", irq_id ), UVM_INFO)
      if (irq_id == 'h0) begin
        // No interrupt greater than threshold
      end
      // Do something ...


      // Complete
      tl_seq(base_addr + rv_plic_reg_pkg::RV_PLIC_CC0_OFFSET, 1'b1, irq_id, rdata);
      `uvm_info(get_name(), $sformatf("IRQ Completed: %d", irq_id ), UVM_INFO)
    end
  endtask : irq_service

endclass : plic_dir_sequence
