// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// SEQUENCE: ibex_mem_intf_slave_seq
//------------------------------------------------------------------------------

class ibex_mem_intf_slave_seq extends uvm_sequence #(ibex_mem_intf_seq_item);

  int                     max_rvalid_delay = 20;
  int                     min_rvalid_delay = 0;
  ibex_mem_intf_seq_item  item;
  mem_model               m_mem;

  `uvm_object_utils(ibex_mem_intf_slave_seq)
  `uvm_declare_p_sequencer(ibex_mem_intf_slave_sequencer)
  `uvm_object_new

  virtual task body();
    if(m_mem ==  null)
      `uvm_fatal(get_full_name(), "Cannot get memory model")
    forever
    begin
      bit [ADDR_WIDTH-1:0] aligned_addr;
      p_sequencer.addr_ph_port.get(item);
      req = ibex_mem_intf_seq_item::type_id::create("req");
      req.randomize() with {
        addr       == item.addr;
        read_write == item.read_write;
        data       == item.data;
        be         == item.be;
        rvalid_delay dist {
          min_rvalid_delay                            :/ 5,
          [min_rvalid_delay+1 : max_rvalid_delay/2-1] :/ 3,
          [max_rvalid_delay/2 : max_rvalid_delay-1]   :/ 1,
          max_rvalid_delay                            :/ 1
        };
      };
      aligned_addr = {req.addr[DATA_WIDTH-1:2], 2'b0};
      if(req.read_write == READ) begin : READ_block
        req.data = m_mem.read(aligned_addr);
      end
      `uvm_info(get_full_name(), $sformatf("Response transfer:\n%0s", req.sprint()), UVM_HIGH)
      start_item(req);
      finish_item(req);
      if(item.read_write == WRITE) begin : WRITE_block
        bit [DATA_WIDTH-1:0] data;
        data = req.data;
        for(int i = 0; i < DATA_WIDTH/8; i++) begin
          if(req.be[i])
            m_mem.write_byte(aligned_addr + i, data[7:0]);
          data = data >> 8;
        end
      end
    end
  endtask : body

endclass : ibex_mem_intf_slave_seq
