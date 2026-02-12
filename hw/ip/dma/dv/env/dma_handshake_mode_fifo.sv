// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This class implements functionality of a simple FIFO
// with a base address, maximum allowed size and enable
class dma_handshake_mode_fifo #(int AddrWidth = bus_params_pkg::BUS_AW,
                                int DataWidth = bus_params_pkg::BUS_DW) extends uvm_object;

  `uvm_object_param_utils(dma_handshake_mode_fifo#(AddrWidth))

  `uvm_object_new

  // Address type used in FIFO accesses; the number of bits is an instance-specific parameter.
  typedef logic [AddrWidth-1:0] mem_addr_t;
  // Byte enables
  typedef logic [DataWidth/8-1:0] mem_mask_t;

  // FIFO variables
  // An SV queue has methods to push or pop data to/from queue.
  // Data is pushed to the front of the FIFO and popped from the back.
  bit [7:0] fifo[$];
  // Enable FIFO
  bit fifo_en;
  // Programmed transfer width
  dma_transfer_width_e per_transfer_width;
  // Size of each non-final chunk of data transferred.
  mem_addr_t chunk_size;
  // Wrap address at the end of each chunk, i.e. _all_ accesses occur to a single address?
  bit wrap;
  // Maximum allowed size of the FIFO; detects excess data being written into FIFO.
  mem_addr_t max_size;
  // Base address of the FIFO
  mem_addr_t fifo_base;
  // Expected address of next access.
  mem_addr_t exp_addr;
  // Byte offset within the current chunk.
  mem_addr_t chunk_offset;

  function void init();
    fifo.delete();
    fifo_en = '0;
    fifo_base = '0;
    max_size = '0;
    chunk_size = '0;
    wrap = 1'b0;
    exp_addr = '0;
    chunk_offset = '0;
  endfunction

  // Enable and configure the FIFO to transfer a chunk of data
  function void enable_fifo(mem_addr_t fifo_base, dma_transfer_width_e per_transfer_width,
                            mem_addr_t chunk_size, bit wrap, mem_addr_t offset,
                            mem_addr_t max_size);
    fifo_en = 1;
    // Configuration of FIFO model.
    this.max_size = max_size;
    this.per_transfer_width = per_transfer_width;
    this.fifo_base = fifo_base;
    this.chunk_size = chunk_size;
    this.wrap = wrap;
    // Current state of data transfer.
    exp_addr = fifo_base;
    chunk_offset = offset % chunk_size;
    if (!wrap) exp_addr += offset - chunk_offset;
  endfunction

  function void disable_fifo();
    fifo_en = 0;
    fifo.delete();
  endfunction

  // Returns the number of items remaining in FIFO
  function int count_bytes_in_queue();
    return fifo.size();
  endfunction

  // Populate the FIFO with the given sequence of pre-randomized source data in preparation
  // for reading
  function void populate_fifo(ref bit [7:0] src_data[],
                              input bit [31:0] offset, input bit [31:0] size);
    `DV_CHECK(fifo_en, "Cannot populate FIFO when it is disabled")

    fifo.delete();
    repeat(size) begin
      fifo.push_front(src_data[offset]);
      offset++;
    end
  endfunction

  // Read a byte from FIFO
  // Reads are done through pop_back to `fifo` object
  function bit [7:0] read_byte(mem_addr_t addr);
    bit [7:0] data;

    `DV_CHECK(fifo_en, "Cannot read data when FIFO is disabled")
    `DV_CHECK(addr[AddrWidth-1:2] == fifo_base[AddrWidth-1:2],
              $sformatf("addr:%0x doesn't match FIFO base address : %0x",
                        addr, fifo_base))

    `DV_CHECK_GT(fifo.size(), 0, "FIFO underflow")
    data = fifo.pop_back();
    return data;
  endfunction

  // Read one or more bytes from the FIFO as part of a TL-UL word read
  //
  // Note: bytes shall be read in Little Endian order ([7:0] through to [31:24] for a 32-bit bus),
  //       which permits us to retain state for non-initial bytes.
  function bit [DataWidth-1:0] read_word_tlul(mem_addr_t addr, mem_mask_t mask);
    // Unfortunately we cannot return X without triggering assertions on the TL-UL bus, so return
    // something identifiable that shall not be used.
    bit [DataWidth-1:0] data = 32'hBAAD_F00D;

    `DV_CHECK(fifo_en, "Cannot read data when FIFO is disabled")
    `DV_CHECK(addr[AddrWidth-1:2] == exp_addr[AddrWidth-1:2] && ~|addr[1:0],
              $sformatf("addr:%0x doesn't match expectation : %0x",
                        addr, exp_addr))

    // Unfortunately we must be tolerant of the fact that only entire 32-bit bus words are
    // requested because of the behavior of 'tlul_adapter_host.' So we must check FIFO underflow
    // at the start of a word read
    `DV_CHECK_EQ(mask, {(DataWidth/8){1'b1}}, "Unexpected read mask")

    // We _must_ have at least one remaining byte or something has gone wrong.
    `DV_CHECK_GT(fifo.size(), 0, "FIFO underflow")
    data[7:0] = fifo.pop_back();

    // Valid FIFO entry must be replicated across the width of the TL-UL bus to ensure that it is
    // presented in whichever data lines the DMA controller consults.
    // (This is unknown because we do not have access to the LSBs of the true read address.)
    case (per_transfer_width)
      DmaXfer1BperTxn: begin
        data = {(DataWidth/8){data[7:0]}};
        chunk_offset++;
      end
      DmaXfer2BperTxn: begin
        if (fifo.size() > 0) data[15:8] = fifo.pop_back();
        // Replicate 2B quantity across bus width
        data = {(DataWidth/16){data[15:0]}};
        chunk_offset += 2;
      end
      default: begin
        `DV_CHECK_EQ(per_transfer_width, DmaXfer4BperTxn, "Invalid FIFO transfer width")
        for (int i = 1; i < 4; i++)
          if (fifo.size() > 0) data[i*8+7 -: 8] = fifo.pop_back();
        // Replicate 4B quantity across bus width
        data = {(DataWidth/32){data[31:0]}};
        chunk_offset += 4;
      end
    endcase
    // Update the transfer state, to form a new address expectation.
    if (chunk_offset >= chunk_size) begin
      chunk_offset = '0;
      if (!wrap) exp_addr += chunk_size;
    end
    return data;
  endfunction

  // Write a byte to FIFO
  // writes are done through push_front to fifo
  function void write_byte(mem_addr_t addr, logic [7:0] data);
    `DV_CHECK(fifo_en, "Cannot write data when FIFO is disabled")
    `DV_CHECK_LT(fifo.size(), max_size, "FIFO overflow")
    `DV_CHECK(addr[AddrWidth-1:2] == exp_addr[AddrWidth-1:2],
              $sformatf("addr:%0x doesn't match expectation : %0x",
                        addr, exp_addr))
    fifo.push_front(data);
    // Update the transfer state, to form a new address expectation.
    chunk_offset++;
    if (chunk_offset >= chunk_size) begin
      chunk_offset = '0;
      if (!wrap) exp_addr += chunk_size;
    end
  endfunction
endclass: dma_handshake_mode_fifo
