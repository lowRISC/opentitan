// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Class containing variables to program all the registers of DMA.
// Constraints are setup such that the randomization is broad and
// any further narrowing can be done in sequences.
// There are additional variables to control the configuration to
// only valid ones and alignment of address values.
//
// The general order of constraint solver is such that the following variables are randomized
// first
// - src_asid
// - dst_asid
// - direction
// - auto_inc_buffer
// - auto_inc_fifo
// - handshake
// - per_transfer_width
//
// Most of the constraints in this file are primarily to limit randomization to
// valid configurations based on valid_dma_config bit.
// If align_address is set, all address variables are aligned to transfer_width
// and the solve order of constraints are setup for this case.
class dma_seq_item extends uvm_sequence_item;

  // Variables to configure DMA
  rand bit auto_inc_buffer;
  rand bit auto_inc_fifo;
  rand bit handshake;
  rand bit [63:0] src_addr;
  rand bit [63:0] dst_addr;
  rand bit [63:0] mem_buffer_almost_limit;
  rand bit [63:0] mem_buffer_limit;
  rand bit [31:0] mem_range_base;
  rand bit [31:0] mem_range_limit;
  rand bit [31:0] total_transfer_size;
  rand mubi4_t mem_range_unlock;
  rand opcode_e opcode;
  rand dma_transfer_width_e per_transfer_width;
  rand asid_encoding_e src_asid;
  rand asid_encoding_e dst_asid;
  rand dma_control_data_direction_e direction;
  // Variable to control which trigger_i signals are active
  rand bit [dma_reg_pkg::NumIntClearSources-1:0] handshake_intr_en;
  // variable used to constrain randomization to only valid configs
  bit valid_dma_config;
  // Variable used to constrain randomization of all addresses values
  // to align with transfer_width
  bit align_address;
  // Bit used to indicate if the configuration is valid
  bit is_valid_config;

  // Use field macros
  `uvm_object_utils_begin(dma_seq_item)
    `uvm_field_int(src_addr, UVM_DEFAULT)
    `uvm_field_int(dst_addr, UVM_DEFAULT)
    `uvm_field_enum(asid_encoding_e, src_asid, UVM_DEFAULT)
    `uvm_field_enum(asid_encoding_e, dst_asid, UVM_DEFAULT)
    `uvm_field_enum(opcode_e, opcode, UVM_DEFAULT)
    `uvm_field_enum(dma_control_data_direction_e, direction, UVM_DEFAULT)
    `uvm_field_int(mem_range_base, UVM_DEFAULT)
    `uvm_field_int(mem_range_limit, UVM_DEFAULT)
    `uvm_field_enum(mubi4_t, mem_range_unlock, UVM_DEFAULT)
    `uvm_field_int(total_transfer_size, UVM_DEFAULT)
    `uvm_field_enum(dma_transfer_width_e, per_transfer_width, UVM_DEFAULT)
    `uvm_field_int(auto_inc_buffer, UVM_DEFAULT)
    `uvm_field_int(auto_inc_fifo, UVM_DEFAULT)
    `uvm_field_int(handshake, UVM_DEFAULT)
    `uvm_field_int(align_address, UVM_DEFAULT)
    `uvm_field_int(is_valid_config, UVM_DEFAULT)
    `uvm_field_int(mem_buffer_almost_limit, UVM_DEFAULT)
    `uvm_field_int(mem_buffer_limit, UVM_DEFAULT)
    `uvm_field_int(handshake_intr_en, UVM_DEFAULT)
  `uvm_object_utils_end

  // Constrain source and destinatination address space ids for valid configurations
  constraint asid_c {
    if (valid_dma_config) {
      // For valid DMA config, either source or destination address space Id must point
      // to OT internal address space
      src_asid == OtInternalAddr || dst_asid == OtInternalAddr;
    }
  }

  constraint mem_range_base_c {
    // Set solve order to make sure mem_range_base is randomized correctly in
    // case align_address is set
    if (align_address) {
      per_transfer_width == DmaXfer2BperTxn -> mem_range_base % 2 == 0;
      per_transfer_width == DmaXfer4BperTxn -> mem_range_base % 4 == 0;
    }
  }

  constraint src_addr_c {
    // Set solve order to make sure source address is randomized correctly in case
    // valid_dma_config or align_address is set
    solve src_asid, per_transfer_width, mem_range_base before src_addr;
    if (valid_dma_config) {
      // If OT internal address space is the source then source address must be
      // greater than the memory base address
      if (src_asid == OtInternalAddr){
        src_addr inside {[mem_range_base : (mem_range_limit - total_transfer_size)]};
      }
      src_asid != SocSystemAddr -> src_addr[63:32] == '0;
    }
    // Address alignment constraint
    if (align_address) {
      per_transfer_width == DmaXfer2BperTxn -> src_addr % 2 == 0;
      per_transfer_width == DmaXfer4BperTxn -> src_addr % 4 == 0;
    }
  }

  constraint dst_addr_c {
    // Set solve order to make sure destination address is randomized correctly in case
    // valid_dma_config or align_address is set
    solve dst_asid, src_asid, mem_range_base before dst_addr;
    if (valid_dma_config) {
      // If OT internal address space is the destination then destination address must be
      // greater than the memory base address
      if (dst_asid == OtInternalAddr) {
        dst_addr inside {[mem_range_base : (mem_range_limit - total_transfer_size)]};
      }
      dst_asid != SocSystemAddr -> dst_addr[63:32] == '0;
    }
    // Address alignment constraint
    if (align_address) {
      per_transfer_width == DmaXfer2BperTxn -> dst_addr % 2 == 0;
      per_transfer_width == DmaXfer4BperTxn -> dst_addr % 4 == 0;
    }
  }

  constraint total_transfer_size_c {
    // Add a soft constrain the total transfer size to limit the amount of time test takes to run
    soft total_transfer_size <= 1024;
  }

  constraint mem_range_limit_c {
    // Set solver order to make sure mem range limit is randomized correctly in case
    // valid_dma_config or align_address is set
    solve mem_range_base, per_transfer_width, total_transfer_size before mem_range_limit;
    // For valid DMA config, address must not exceed mem_range_limit.
    // So, mem_range_limit must at least be greater than total_transfer_size from mem_range_base
    if (valid_dma_config) {
      mem_range_limit >= (mem_range_base + total_transfer_size);
    }
    if (align_address) {
      per_transfer_width == DmaXfer2BperTxn -> mem_range_limit % 2 == 0;
      per_transfer_width == DmaXfer4BperTxn -> mem_range_limit % 4 == 0;
    }
  }

  constraint mem_buffer_limit_c {
    // Set solver order to make sure mem buffer limit is randomized correctly in case
    // valid_dma_config or align_address is set
    solve handshake, dst_addr, per_transfer_width before mem_buffer_limit;
    // For valid dma config, mem buffer limit must be greater than destination address
    // in order to detect overflow
    if (valid_dma_config) {
       if (handshake) {
         mem_buffer_limit > dst_addr;
       }
    }
    if (align_address) {
      per_transfer_width == DmaXfer2BperTxn -> mem_buffer_limit % 2 == 0;
      per_transfer_width == DmaXfer4BperTxn -> mem_buffer_limit % 4 == 0;
    }
  }

  constraint mem_buffer_almost_limit_c {
    // Set solver order to make sure mem buffer almost limit is randomized correctly
    // in case valid_dma_config or align_address is set
    solve handshake, dst_addr, per_transfer_width before mem_buffer_almost_limit;
    // For valid dma config, mem buffer almost limit must not be
    // less than destionation address
    if (valid_dma_config) {
       if (handshake) {
         mem_buffer_almost_limit > dst_addr;
       }
    }
    if (align_address) {
      per_transfer_width == DmaXfer2BperTxn -> mem_buffer_almost_limit % 2 == 0;
      per_transfer_width == DmaXfer4BperTxn -> mem_buffer_almost_limit % 4 == 0;
    }
  }

  constraint mem_range_unlock_c {
    // For valid DMA configurations, memory range register must be locked
    if (valid_dma_config) {
      mem_range_unlock == MuBi4False;
    }
  }

  constraint handshake_intr_en_c {
    solve handshake before handshake_intr_en;
    // For valid dma confiugurations, enable at least one handshake interrupt
    if (valid_dma_config) {
      if (handshake) {
        handshake_intr_en != 0;
      }
    }
  }

  //  Constructor: new
  function new(string name = "");
    super.new(name);
    valid_dma_config = 0;
    align_address = 0;
  endfunction : new

  // Function to disable randomization of memory range register and lock register.
  // This is expected to be used to explore only valid DMA configurations since
  // DMA memory range registers needs to be locked and can only be modified after reset.
  function void lock_memory_range();
    mem_range_base.rand_mode(0);
    mem_range_limit.rand_mode(0);
    mem_range_unlock.rand_mode(0);
    mem_range_unlock_c.constraint_mode(0);
    `uvm_info(`gfn, $sformatf("Disable randomisation of mem_range_base and mem_range_limit"),
              UVM_HIGH)
  endfunction

  function void post_randomize();
    super.post_randomize();
    // Check if randomization leads to valid configuration
    is_valid_config = check_config();
    `uvm_info(`gfn, $sformatf("[DMA] dma_seq_item:%s", convert2string()), UVM_MEDIUM)
  endfunction : post_randomize

  // Function to check if provided address and size is in DMA memory region
  function bit is_address_in_dma_memory_region(bit [31:0] address);
    return ((address >= mem_range_base) && (address <= mem_range_limit));
  endfunction

  // Function to check if the programmed DMA settings are valid.
  //   if settings are valid (returns 1), expected request queue must be populated
  //   else (returns 0) queue will not be updated
  function bit check_config();
    bit valid_config = 1;
    // Check if operation is valid
    case (opcode)
      OpcCopy: begin  // Do nothing as this is valid OP code
      end
      default: begin
        `uvm_info(`gfn, $sformatf("Unsupported DMA operation: %s", opcode.name()), UVM_MEDIUM)
        valid_config = 0;
      end
    endcase
    // Check if operation is performed between valid source and destination combinations
    // For all valid configurations, either source or destination address space Id must point
    // to OT internal address space
    if (src_asid == OtInternalAddr) begin
      if (!is_address_in_dma_memory_region(src_addr[31:0])) begin
        // If source address space ID points to OT internal address space,
        // it must be within DMA enabled address range.
        `uvm_info(`gfn,
                $sformatf(
                  "Invalid src addr range found lo: %08x hi: %08x with base: %08x limit: %0x",
                  src_addr[31:0], src_addr[63:32], mem_range_base, mem_range_limit),
                UVM_MEDIUM)
        valid_config = 0;
      end
    end else if (dst_asid == OtInternalAddr) begin
      // If destination address space ID points to OT internal address space
      // it must be within DMA enabled address range.
      if (!is_address_in_dma_memory_region(dst_addr[31:0])) begin
        `uvm_info(`gfn,
                  $sformatf(
                    "Invalid dst addr range found lo: %08x hi: %08x with base: %08x limit: %0x",
                    dst_addr[31:0], dst_addr[63:32], mem_range_base, mem_range_limit),
                  UVM_MEDIUM)
        valid_config = 0;
      end
    end else begin
      // OT internal address space is neither source nor destination for the operation
      `uvm_info(`gfn, $sformatf("Invalid source : %s and destination : %s combination",
                                src_asid.name(), dst_asid.name()), UVM_MEDIUM)
      valid_config = 0;
    end
    // Check if memory range is locked
    if (mem_range_unlock == MuBi4True) begin
      `uvm_info(`gfn, "Memory range registers unlocked", UVM_MEDIUM)
      valid_config = 0;
    end
    return valid_config;
  endfunction: check_config

  // Method to convert transfer width to a corresponding value for the a_size field
  function uint transfer_width_to_a_size(dma_transfer_width_e width);
    case (width)
      DmaXfer1BperTxn: return 0;
      DmaXfer2BperTxn: return 1;
      DmaXfer4BperTxn: return 2;
      default: `uvm_fatal(`gfn, $sformatf("Unexpected transfer width %d", width))
    endcase
  endfunction

  // Method to convert transfer_width enum to number of bytes per transfer
  function uint transfer_width_to_num_bytes(dma_transfer_width_e width);
    case (width)
      DmaXfer1BperTxn: return 1;
      DmaXfer2BperTxn: return 2;
      DmaXfer4BperTxn: return 4;
      default: `uvm_fatal(`gfn, $sformatf("Unexpected transfer width %d", width))
    endcase
  endfunction

  // Reset all variable values
  function void reset_config();
    src_addr = 0;
    dst_addr = 0;
    src_asid = OtInternalAddr;
    dst_asid = OtInternalAddr;
    opcode = OpcCopy;
    direction = DmaRcvData;
    mem_range_base = 0;
    mem_range_limit = 0;
    total_transfer_size = 0;
    per_transfer_width = DmaXfer1BperTxn;
    auto_inc_buffer = 0;
    auto_inc_fifo = 0;
    handshake = 0;
    // reset non random variables
    valid_dma_config = 0;
    align_address = 0;
  endfunction

  // Disable randomization of all variables
  function void disable_randomization();
    src_addr.rand_mode(0);
    dst_addr.rand_mode(0);
    src_asid.rand_mode(0);
    dst_asid.rand_mode(0);
    opcode.rand_mode(0);
    direction.rand_mode(0);
    mem_range_base.rand_mode(0);
    mem_range_limit.rand_mode(0);
    total_transfer_size.rand_mode(0);
    per_transfer_width.rand_mode(0);
    auto_inc_buffer.rand_mode(0);
    auto_inc_fifo.rand_mode(0);
    handshake.rand_mode(0);
  endfunction

  // Return if Read address increment is disabled
  function bit get_read_fifo_en();
    return handshake && // Handshake mode enabled
           direction == DmaRcvData && // Read from FIFO
           !auto_inc_fifo; // FIFO address auto increment disabled
  endfunction

  // Return if Write address increment is disabled
  function bit get_write_fifo_en();
    return handshake && // Handshake mode enabled
           direction == DmaSendData && // Write to FIFO
           !auto_inc_fifo; // FIFO address auto increment disabled
  endfunction

endclass : dma_seq_item
