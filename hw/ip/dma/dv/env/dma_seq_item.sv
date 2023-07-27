// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_seq_item extends uvm_sequence_item;
  `uvm_object_utils(dma_seq_item)

  rand bit [63:0] m_src_addr;
  rand bit [63:0] m_dst_addr;
  rand bit [1:0]  m_src_asid;
  rand bit [1:0]  m_dst_asid;
  rand bit [1:0]  m_opcode = dma_env_pkg::DmaOperCopy;
  rand bit        m_direction;
  rand bit [31:0] m_mem_range_base;
  rand bit [31:0] m_mem_range_limit;
  rand bit [31:0] m_total_transfer_size;
  rand bit [31:0] m_per_transfer_size;
  rand bit        m_auto_inc_buffer;
  rand bit        m_auto_inc_fifo;
  rand bit        m_handshake;


  // Constraint : Address Specific ID (ASID)
  //      ASID=0 will trigger transactions on HOST
  //      ASID=1 will trigger transactions on XBAR
  //      ASID=2 will trigger transactions on SYS
  //      ASID=3 will trigger transactions on XBAR
  constraint dma_addressing_c {
    // ASID specific
    if (m_src_asid != 2) m_src_addr[63:32] == 32'd0; // Only SYS transactions can go over 4GB space
    if (m_dst_asid != 2) m_dst_addr[63:32] == 32'd0; // Only SYS transactions can go over 4GB space

    // Address alignment
    m_src_addr[1:0] == 2'b00; // 32b alignment (at least for the first transaction)
    m_dst_addr[1:0] == 2'b00;
    m_mem_range_base[1:0] == 2'b00;
    m_mem_range_limit[1:0] == 2'b00;

    // Address range check
    if (m_src_asid == 0) {
      // If source is within OT Internal Address Space,
      m_src_addr >= m_mem_range_base;
      //   make sure we randomize within base and limit
      (m_src_addr + m_total_transfer_size) <= m_mem_range_limit;
    }
    if (m_dst_asid == 0) {
      // Same as above for the destination
      m_dst_addr >= m_mem_range_base;
      (m_dst_addr + m_total_transfer_size) <= m_mem_range_limit;
    }
    m_mem_range_base + m_total_transfer_size < m_mem_range_limit;

    // Data movement check
    (m_src_asid == 2'b00 && (m_dst_asid == 2'b10 || m_dst_asid == 2'b01)) ->
      ((m_dst_addr[31:0] <= m_mem_range_limit) && (m_dst_addr[31:0] > m_mem_range_base));
    (m_dst_asid == 2'b00 && (m_src_asid == 2'b10 || m_src_asid == 2'b01)) ->
      ((m_src_addr[31:0] <= m_mem_range_limit) && (m_src_addr[31:0] > m_mem_range_base));
  }

  constraint dma_sane_data_size_c {
    // Smaller and sane transfer size
    m_total_transfer_size <= 64;
    (m_total_transfer_size % m_per_transfer_size) == 0;
    m_total_transfer_size >= m_per_transfer_size;
  }

  constraint dma_handshake_c {
    soft m_handshake == 0;
  }

  constraint dma_if_no_handshake_c {
    if (m_handshake) {
      if (m_direction == 0) {
        soft m_auto_inc_buffer == 1;
        soft m_auto_inc_fifo == 0;
      } else {
        soft m_auto_inc_buffer == 0;
        soft m_auto_inc_fifo == 1;
      }
    } else {
      soft m_auto_inc_buffer == 0;
      soft m_auto_inc_fifo == 0;
    }
  }

  // Constraint to disable SYS
  constraint dma_disable_sys_c {
    soft m_src_asid != 2'b10;
    soft m_dst_asid != 2'b10;
  }

  //  Constructor: new
  function new(string name = "dma_seq_item");
    super.new(name);
  endfunction: new

  function void post_randomize();
    super.post_randomize();

    `uvm_info(`gfn, $sformatf("[DMA] dma_seq_item:%s", convert2string()), UVM_HIGH)
  endfunction: post_randomize

  function string convert2string();
    return {"\n",
      $sformatf("Src. Addr.:     0x%016h\n", m_src_addr),
      $sformatf("Dst. Addr.:     0x%016h\n", m_dst_addr),
      $sformatf("Range Base:     0x%08h\n", m_mem_range_base),
      $sformatf("Range Limit:    0x%08h\n", m_mem_range_limit),
      $sformatf("Src. ASID.:     %d\n", m_src_asid),
      $sformatf("Dst. ASID.:     %d\n", m_dst_asid),
      $sformatf("Opcode:         %d\n", m_opcode),
      $sformatf("Direction:      %d\n", m_direction),
      $sformatf("AutoInc Buffer: %d\n", m_auto_inc_buffer),
      $sformatf("AutoInc FIFO:   %d\n", m_auto_inc_fifo)
    };
  endfunction
endclass: dma_seq_item
