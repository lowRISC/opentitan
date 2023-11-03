// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This class implements functionality of a simple FIFO
// with a base address, maximum allowed size and enable
class dma_handshake_mode_fifo #(int AddrWidth = bus_params_pkg::BUS_AW) extends uvm_object;

  `uvm_object_param_utils(dma_handshake_mode_fifo#(AddrWidth))

  `uvm_object_new

  typedef logic [AddrWidth-1:0] mem_addr_t;

  // FIFO variables
  // As SV queue has methods to push or pop data from queue
  // Data is pushed to the front of the FIFO and popped from the back.
  bit [7:0] fifo[$];
  // Enable FIFO
  bit fifo_en;
  // Maximum allowed size of the FIFO
  mem_addr_t max_size;
  // Base address of the FIFO
  mem_addr_t fifo_base;

  function void init();
    fifo.delete();
    fifo_en = '0;
    fifo_base = '0;
    max_size = '0;
  endfunction

  function void enable_fifo(mem_addr_t fifo_base, mem_addr_t max_size);
    fifo_en = 1;
    this.max_size = max_size;
    this.fifo_base = fifo_base;
  endfunction

  function void disable_fifo();
    fifo_en = 0;
    fifo.delete();
  endfunction

  // Returns the number of items remaining in FIFO
  function int count_bytes_in_queue();
    return fifo.size();
  endfunction

  // Method to randomise data in queue, with the given size
  function void randomise_data(mem_addr_t size);
    `DV_CHECK(fifo_en, "Cannot randomize data when FIFO is disabled")

    if (size <= max_size) begin
      repeat(size) begin
        fifo.push_back($urandom_range(0,255));
      end
    end else begin
      `uvm_error(`gfn, $sformatf("size:%0d greater than FIFO max size %0d", size, max_size))
    end
  endfunction

  // Read a byte from FIFO
  // Reads are done through pop_back to `fifo` object
  function bit [7:0] read_byte(mem_addr_t addr);
    `DV_CHECK(fifo_en, "Cannot read data when FIFO is disabled")
    `DV_CHECK_GT(fifo.size(), 0, "FIFO underflow")
    `DV_CHECK(addr[AddrWidth-1:2] == fifo_base[AddrWidth-1:2],
              $sformatf("addr:%0x doesnt match FIFO base address : %0x",
                        addr, fifo_base))
    return fifo.pop_back();
  endfunction

  // Write a byte to FIFO
  // writes are done through push_front to fifo
  function void write_byte(mem_addr_t addr, logic [7:0] data);
    `DV_CHECK(fifo_en, "Cannot write data when FIFO is disabled")
    `DV_CHECK_LT(fifo.size(), max_size, "FIFO overflow")
    `DV_CHECK(addr[AddrWidth-1:2] == fifo_base[AddrWidth-1:2],
              $sformatf("addr:%0x doesn't match FIFO base address : %0x",
                        addr, fifo_base))
    fifo.push_front(data);
  endfunction
endclass: dma_handshake_mode_fifo
