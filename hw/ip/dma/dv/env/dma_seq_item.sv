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
// Then the memory range is randomized
// - mem_range_base
// - mem_range_limit
// Finally the addresses of data to be transferred, if the configuration must be valid
// - chunk_data_size
// - total_data_size
// decided before source buffer, to assist in meeting memory range requirement:
// - src_addr
// decided before destination buffer, to assist in preventing overlap with source:
// - dst_addr
//
// Most of the constraints in this file are primarily to limit randomization to
// valid configurations based on valid_dma_config bit.
class dma_seq_item extends uvm_sequence_item;

  // Variables to configure DMA
  rand bit auto_inc_buffer;
  rand bit auto_inc_fifo;
  rand bit handshake;
  rand bit [63:0] src_addr;
  rand bit [63:0] dst_addr;
  rand bit [63:0] dst_addr_almost_limit;
  rand bit [63:0] dst_addr_limit;
  rand bit        mem_range_valid;
  rand bit [31:0] mem_range_base;
  rand bit [31:0] mem_range_limit;
  rand bit [31:0] total_data_size;
  rand bit [31:0] chunk_data_size;
  rand mubi4_t range_regwen;
  rand opcode_e opcode;
  rand dma_transfer_width_e per_transfer_width;
  rand asid_encoding_e src_asid;
  rand asid_encoding_e dst_asid;
  rand dma_control_data_direction_e direction;
  // Variable to indicate if interrupt needs clearing before reading from FIFO
  rand bit [dma_reg_pkg::NumIntClearSources-1:0] clear_intr_src;
  // Variable to indicate the bus on which each interrupt clearing address resides
  // 0 - CTN/SYS fabric
  // 1 - OT internal
  rand bit [dma_reg_pkg::NumIntClearSources-1:0] clear_intr_bus;
  // Array with interrupt register addresses
  // size of array will be number of Handshake interrupts(dma_reg_pkg::NumIntClearSources)
  rand bit [31:0] intr_src_addr[];
  // Array with interrupt register value to clear interrupt
  // size of array will be number of Handshake interrupts(dma_reg_pkg::NumIntClearSources)
  rand bit [31:0] intr_src_wr_val[];
  // Initial value of SHA digest
  // size of array will be 16 to support SHA256, SHA-382 and SHA512 algorithms
  rand bit [31:0] sha2_digest[];
  // Variable to control which trigger_i signals are active
  rand lsio_trigger_t handshake_intr_en;

  // variable used to constrain randomization to only valid configs
  bit valid_dma_config;
  // Waive testing of the system bus within this DV environment?
  bit dma_dv_waive_system_bus;

  // Bit used to indicate if the configuration is valid
  bit is_valid_config;
  // LSIO trigger input value to be driven from testbench
  rand bit [dma_reg_pkg::NumIntClearSources - 1:0] lsio_trigger_i;

  // Use field macros
  `uvm_object_utils_begin(dma_seq_item)
    `uvm_field_int(src_addr, UVM_DEFAULT)
    `uvm_field_int(dst_addr, UVM_DEFAULT)
    `uvm_field_enum(asid_encoding_e, src_asid, UVM_DEFAULT)
    `uvm_field_enum(asid_encoding_e, dst_asid, UVM_DEFAULT)
    `uvm_field_enum(opcode_e, opcode, UVM_DEFAULT)
    `uvm_field_enum(dma_control_data_direction_e, direction, UVM_DEFAULT)
    `uvm_field_int(mem_range_valid, UVM_DEFAULT)
    `uvm_field_int(mem_range_base, UVM_DEFAULT)
    `uvm_field_int(mem_range_limit, UVM_DEFAULT)
    `uvm_field_enum(mubi4_t, range_regwen, UVM_DEFAULT)
    `uvm_field_int(total_data_size, UVM_DEFAULT)
    `uvm_field_int(chunk_data_size, UVM_DEFAULT)
    `uvm_field_enum(dma_transfer_width_e, per_transfer_width, UVM_DEFAULT)
    `uvm_field_int(auto_inc_buffer, UVM_DEFAULT)
    `uvm_field_int(auto_inc_fifo, UVM_DEFAULT)
    `uvm_field_int(handshake, UVM_DEFAULT)
    `uvm_field_int(is_valid_config, UVM_DEFAULT)
    `uvm_field_int(dst_addr_almost_limit, UVM_DEFAULT)
    `uvm_field_int(dst_addr_limit, UVM_DEFAULT)
    `uvm_field_int(handshake_intr_en, UVM_DEFAULT)
    `uvm_field_int(clear_intr_src, UVM_DEFAULT)
    `uvm_field_int(clear_intr_bus, UVM_DEFAULT)
    `uvm_field_array_int(intr_src_addr, UVM_DEFAULT)
    `uvm_field_array_int(intr_src_wr_val, UVM_DEFAULT)
    `uvm_field_array_int(sha2_digest, UVM_DEFAULT)
  `uvm_object_utils_end

  constraint lsio_trigger_i_c {
    // Hardware handshaking sequences will not operate without at least one enabled interrupt source
    // to keep the data flowing.
    solve handshake_intr_en before lsio_trigger_i;
    (lsio_trigger_i & handshake_intr_en) != 0;
  }

  // SHA hashing supports only 4-byte transactions
  constraint transfer_width_c {
    if (valid_dma_config) {
      opcode inside {OpcSha256, OpcSha384, OpcSha512} -> per_transfer_width == DmaXfer4BperTxn;
    }
  }

  // Constrain the size of sha digest array to support SHA-256, SHA-382 and SHA-512
  constraint sha2_digest_c {
    sha2_digest.size() == 16;
  }

  // Constrain array size to number of handshake interrupt signals
  constraint intr_src_addr_c {
    intr_src_addr.size() == dma_reg_pkg::NumIntClearSources;
  }

  // Constrain array size to number of handshake interrupt signals
  constraint intr_src_wr_val_c {
    intr_src_wr_val.size() == dma_reg_pkg::NumIntClearSources;
  }

  // Constrain source and destinatination address space ids for valid configurations
  constraint asid_c {
    if (dma_dv_waive_system_bus) {
      // There is no model of the SoC System bus, so attempting any transaction to that bus will
      // result in the DMA controller stalling
      src_asid != SocSystemAddr;
      dst_asid != SocSystemAddr;
    }
  }

  constraint src_addr_c {
    // Set solve order to make sure source address is randomized correctly in case
    // valid_dma_config is set
    solve mem_range_base, mem_range_limit before src_addr;
    if (valid_dma_config) {
      // If OT internal address space is the source, data is being exported, and the memory
      // window is enabled, then ensure all source addresses lie within the window
      if (mem_range_valid && src_asid == OtInternalAddr && dst_asid != OtInternalAddr) {
        src_addr >= mem_range_base;
        src_addr <= mem_range_limit;
        mem_range_limit - src_addr >= chunk_data_size;
        // If auto increment is not used on the memory end of the operation then successive chunks
        // overlap each other, but in other cases the entire transfer must fit within the window
        if (!handshake || (direction == DmaRcvData && auto_inc_buffer)) {
          mem_range_limit - src_addr >= total_data_size;
        }
      }
      // For valid configurations, the source address must be aligned to the transfer width.
      per_transfer_width == DmaXfer4BperTxn -> src_addr[1:0] == 2'd0;
      per_transfer_width == DmaXfer2BperTxn -> src_addr[0] == 1'b0;
      // Only the SoC System bus has a full 64-bit address space.
      src_asid != SocSystemAddr -> src_addr[63:32] == '0;
    }
  }

  constraint dst_addr_c {
    // Set solve order to make sure destination address is randomized correctly in case
    // valid_dma_config is set.
    //
    // Ensure that the source buffer has been decided already, so that we can prevent this
    // destination buffer overlapping it.
    solve src_addr before dst_addr;
    if (valid_dma_config) {
      // If OT internal address space is the destination, data is being imported, and the memory
      // window is enabled, then ensure all destination addresses lie within the window
      if (mem_range_valid && dst_asid == OtInternalAddr && src_asid != OtInternalAddr) {
        dst_addr >= mem_range_base;
        dst_addr <= mem_range_limit;
        mem_range_limit - dst_addr >= chunk_data_size;
        // If auto increment is not used on the memory end of the operation, then successive chunks
        // overlap each other, but in other cases the entire transfer must fit within the window
        if (!handshake || (direction == DmaSendData && auto_inc_buffer)) {
          mem_range_limit - dst_addr >= total_data_size;
        }
        if (src_asid == OtInternalAddr) {
          // Avoid overlap between source and destination buffers, also leaving a slight gap so
          // that any out-of-bounds access does not hit a contiguous buffer
          //
          // `total_data_size` here is often larger than the valid addressable range in
          // handshake mode, but keeps things simpler
          (dst_addr > src_addr + total_data_size + 'h10) ||
          (src_addr > dst_addr + total_data_size + 'h10);
        }
      }
      // For valid configurations, the destination address must be aligned to the transfer width.
      per_transfer_width == DmaXfer4BperTxn -> dst_addr[1:0] == 2'd0;
      per_transfer_width == DmaXfer2BperTxn -> dst_addr[0] == 1'b0;
      // Only the SoC System bus has a full 64-bit address space.
      dst_asid != SocSystemAddr -> dst_addr[63:32] == '0;
    }
  }

  constraint total_data_size_c {
    solve mem_range_limit before total_data_size;
    if (valid_dma_config) {
      total_data_size <= mem_range_limit - mem_range_base;
    }
    // Add a soft constraint on the total transfer size to limit the test run time
    soft total_data_size inside {[1:1024]};
  }

  constraint chunk_data_size_c {
    solve mem_range_limit before chunk_data_size;
    if (valid_dma_config) {
      chunk_data_size <= mem_range_limit - mem_range_base;
    }
    if (handshake) {
      // Add a soft constraint to model realistic FIFO transfers; smaller, more frequent transfers
      // are more susceptible to races in interrupt generation/handling
      soft chunk_data_size inside {[1:256]};
    }
    // For non-final chunks in a 4B-wide transfer, the chunk size must ensure that updated
    // source/destination addresses meet the alignment requirements for the start of the next
    // chunk.
    // For narrower handshaking transfers, there is also a 4n requirement on the chunk size when
    // the FIFO address end does not advance, to keep the source and destination alignments equal
    if (per_transfer_width == DmaXfer4BperTxn || (handshake && !auto_inc_fifo)) {
      chunk_data_size[1:0] == '0;
    } else {
      per_transfer_width == DmaXfer2BperTxn -> chunk_data_size[0] == 1'b0;
    }

    if (chunk_data_size < total_data_size) {
      // SHA2 can accept a partial 32-bit word only at the very end of the message being hashed,
      // so non-final transfers must have a size of 4n. Since 4B/txn mode demands 4n alignment
      // already, constraining the chunk size is enough to guarantee 4n alignment of the chunk end.
      opcode inside {OpcSha256, OpcSha384, OpcSha512} -> chunk_data_size[1:0] == 2'b00;

      // Source and destination addresses must have the same alignment at the start of non-initial
      // chunks when addresses advance
      !handshake || auto_inc_buffer -> chunk_data_size[1:0] == 2'b00;
    }

    // Chunk size must be a multiple of the bytes/transaction
    // TODO: perhaps only for 'valid_dma_config' if at some point the DMAC enforces this
    if (chunk_data_size < total_data_size) {
      per_transfer_width == DmaXfer4BperTxn -> chunk_data_size[1:0] == 2'd0;
      per_transfer_width == DmaXfer2BperTxn -> chunk_data_size[0] == 1'b0;
    }
  }

  constraint mem_range_valid_c {
    if (valid_dma_config) {
      // Note: The DMA controller insists upon the `range_valid` bit being set before it will accept
      // any operation. This does not mean the range must be 'locked.'
      mem_range_valid == 1'b1;
    }
  }

  constraint mem_range_limit_c {
    // Set solver order to make sure mem range limit is randomized correctly in case
    // valid_dma_config is set
    solve mem_range_base before mem_range_limit;
    // For valid DMA config, [mem_range_base, mem_range_limit) describes the addressable memory
    // window, but it need not always be enabled, and only applies to transfers crossing the divide
    // (importing to/exporting from OT)
    if (valid_dma_config && mem_range_valid) {
      // Note: The DMA controller insists upon checking that a valid range has been specified
      // before it will accept any operation.
      mem_range_limit >= mem_range_base;
    }
  }

  constraint dst_addr_limit_c {
    // Set solver order to make sure mem buffer limit is randomized correctly in case
    // valid_dma_config is set
    solve dst_addr_almost_limit before dst_addr_limit;
    // For valid dma config, mem buffer limit must be greater than destination address
    // in order to detect passing the limit
    if (valid_dma_config) {
       if (handshake && direction == DmaRcvData) {
          dst_addr_limit > dst_addr_almost_limit;
       }
    }
  }

  constraint dst_addr_almost_limit_c {
    // Set solver order to make sure mem buffer almost limit is randomized correctly
    // in case valid_dma_config is set
    solve dst_addr before dst_addr_almost_limit;
    // For valid dma config, mem buffer almost limit must not be
    // less than destination address
    if (valid_dma_config) {
       if (handshake && direction == DmaRcvData) {
          dst_addr_almost_limit > dst_addr;
       }
    }
  }

  constraint range_regwen_c {
    // For valid DMA configurations, the memory range registers _may_ be locked but this is not
    // obligatory. Having the separate 'RANGE_VALID' bit affords the opportunity for FW at
    // different stages within the boot process to employ different address ranges.
    if (!valid_dma_config) {
      // We need to keep this True to prevent subsequent randomization failures; the REGWEN can
      // only be restored to True (permitting changes) by an IP block reset.
      range_regwen == MuBi4True;
    }
  }

  constraint handshake_intr_en_c {
    solve handshake before handshake_intr_en;
    // For valid dma configurations, enable at least one handshake interrupt
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
  endfunction : new

  // Function to disable randomization of memory range register and lock register.
  // This is expected to be used to explore only valid DMA configurations since
  // DMA memory range registers needs to be locked and can only be modified after reset.
  function void lock_memory_range();
    mem_range_base.rand_mode(0);
    mem_range_limit.rand_mode(0);
    range_regwen.rand_mode(0);
    range_regwen_c.constraint_mode(0);
    `uvm_info(`gfn, $sformatf("Disable randomisation of mem_range_base and mem_range_limit"),
              UVM_HIGH)
  endfunction

  // We need to position the 'Clear Interrupt' addresses such that they are disjoint with each other
  // and with the source and destination buffers
  function bit choose_intr_src_addrs();
    `uvm_info(`gfn, "Randomizing 'clear interrupt' addresses", UVM_HIGH)
    for (uint i = 0; i < intr_src_addr.size(); i++) begin
      const uint max_tries = 100;
      uint tries = 0;
      // Only try so many attempts, to keep things time-bounded
      while (tries < max_tries) begin
        // Choose a 4B-aligned address; TL-UL accesses discard [1:0] on 32-bit bus.
        bit [31:0] cand = $urandom & ~3;
        const uint gap = 'h10;
        // Here are we treating all interrupt sourcers and buffers as if they belonged to a single
        // memory space, to avoid further complicating the code
        //
        // Check against the memory buffers, again leaving a small gap to reduce confusion
        if ((cand + gap < src_addr || cand > src_addr + total_data_size + gap) &&
            (cand + gap < dst_addr || cand > dst_addr + total_data_size + gap)) begin
          uint j = i;
          // Check against all of the addresses so far decided
          while (j > 0 && intr_src_addr[j] != cand) begin
            j--;
          end
          if (!j) begin
            // This candidate is acceptable
            intr_src_addr[i] = cand;
            break;
          end
        end
      end
      if (tries >= max_tries) begin
        // Failed to choose suitable addresses
        return 1'b0;
      end
    end
    `uvm_info(`gfn, "Finished randomizing 'clear interrupt' addresses", UVM_HIGH)
    return 1'b1;
  endfunction

  virtual function string convert2string();
    // Controller configuration
    string str = {
        $sformatf("\n\tmem_range_valid         : %0d",    mem_range_valid),
        $sformatf("\n\tmem_range_base          : 0x%08x", mem_range_base),
        $sformatf("\n\tmem_range_limit         : 0x%08x", mem_range_limit),
        $sformatf("\n\tdst_addr_almost_limit   : 0x%16x", dst_addr_almost_limit),
        $sformatf("\n\tdst_addr_limit          : 0x%16x", dst_addr_limit),
        $sformatf("\n\tclear_intr_src          : 0x%8x",  clear_intr_src),
        $sformatf("\n\tclear_intr_bus          : 0x%8x",  clear_intr_bus),
        $sformatf("\n\thandshake_intr_en       : 0x%08x", handshake_intr_en),
        $sformatf("\n\tlsio_trigger_i          : 0x%08x", lsio_trigger_i)
    };

    // Transfer mode
    str = {str,
        $sformatf("\n\thandshake               : %0d", handshake),
        $sformatf("\n\tdirection               : %0d", direction),
        $sformatf("\n\tauto_inc_fifo           : %0d", auto_inc_fifo),
        $sformatf("\n\tauto_inc_buffer         : %0d", auto_inc_buffer)
    };

    // Transfer properties
    str = {str,
        $sformatf("\n\tsrc_asid                : %x",     src_asid),
        $sformatf("\n\tdst_asid                : %x",     dst_asid),
        $sformatf("\n\tsrc_addr                : 0x%16x", src_addr),
        $sformatf("\n\tdst_addr                : 0x%16x", dst_addr),
        $sformatf("\n\topcode                  : %0d",    opcode),
        $sformatf("\n\tper_transfer_width      : %0d",    per_transfer_width),
        $sformatf("\n\tchunk_data_size         : 0x%x",   chunk_data_size),
        $sformatf("\n\ttotal_data_size         : 0x%x",   total_data_size)
    };

    // Verdict on whether this is a valid DMA configuration, eg. post-randomization
    str = {str,
        $sformatf("\n\n\t=> Valid: %0d", is_valid_config)
    };
    return str;
  endfunction

  function void post_randomize();
    super.post_randomize();
    // Check if randomization leads to valid configuration
    is_valid_config = choose_intr_src_addrs();
    if (is_valid_config) begin
      is_valid_config = check_config("post-randomization");
    end
    `uvm_info(`gfn, $sformatf("[DMA] randomized dma_seq_item:%s", convert2string()), UVM_MEDIUM)
  endfunction : post_randomize

  // Function to check if provided address and size is in DMA memory region
  function bit is_address_in_dma_memory_region(bit [31:0] address);
    // Note: both the base and the limit addresses are inclusive.
    return ((address >= mem_range_base) && (address <= mem_range_limit));
  endfunction

  // Is a buffer of the given base address and size fully contained within the DMA-enabled memory
  // range?
  function bit is_buffer_in_dma_memory_region(bit [31:0] base, bit [31:0] size);
    return (is_address_in_dma_memory_region(base) &&
            is_address_in_dma_memory_region(base + size - 1'b1));
  endfunction

  // Function to check if the programmed DMA settings are valid.
  //   if settings are valid (returns 1), expected request queue must be populated
  //   else (returns 0) queue will not be updated
  function bit check_config(string reason = "");
    bit [31:0] memory_range;
    bit [1:0] align_mask;
    bit valid_config = 1;

    `uvm_info(`gfn, $sformatf("Checking configuration (%s)", reason), UVM_MEDIUM)
    // Each check is performed independently and reported, to produce a complete list of reasons
    // that the configuration is invalid.

    // Testing of the System bus may be waived in this DV environment
    if (!dma_dv_waive_system_bus && (src_asid == SocSystemAddr || dst_asid == SocSystemAddr)) begin
      `uvm_info(`gfn, " - SoCSystemAddr is NOT yet implemented", UVM_MEDIUM)
      valid_config = 0;
    end

    // Check that the ASIDs are valid
    if (!(dst_asid inside {OtInternalAddr, SocControlAddr, SocSystemAddr})) begin
      `uvm_info(`gfn, " - Destination ASID invalid", UVM_MEDIUM)
      valid_config = 0;
    end
    if (!(src_asid inside {OtInternalAddr, SocControlAddr, SocSystemAddr})) begin
      `uvm_info(`gfn, " - Source ASID invalid", UVM_MEDIUM)
      valid_config = 0;
    end

    // Check if operation is valid
    if (opcode inside {OpcSha256, OpcSha384, OpcSha512}) begin
      if (per_transfer_width != DmaXfer4BperTxn) begin
        `uvm_info(`gfn, $sformatf(" - SHA hashing operates only on 4B/txn"), UVM_MEDIUM)
        valid_config = 0;
      end
    end else if (opcode != OpcCopy) begin
      `uvm_info(`gfn, $sformatf(" - Unsupported DMA operation: %s", opcode.name()), UVM_MEDIUM)
      valid_config = 0;
    end

    // The DMA-enabled memory range must have been set up, even though it may not be used
    if (!mem_range_valid) begin
      `uvm_info(`gfn, " - Valid DMA enabled memory range has not been set up", UVM_MEDIUM)
      valid_config = 0;
    end
    // Check the validity of the DMA-enabled memory range
    // Note: the base and limit addresses are both inclusive
    if (mem_range_valid && !(mem_range_base <= mem_range_limit)) begin
      `uvm_info(`gfn, " - DMA-enabled memory range invalid but enabled", UVM_MEDIUM)
      valid_config = 0;
    end

    // Ascertain the size of the in-memory buffer
    memory_range = total_data_size;
    if (handshake && !auto_inc_buffer) begin
      memory_range = chunk_data_size;  // All chunks overlap each other
    end

    // Check if operation is performed between valid source and destination combinations
    // For all valid configurations, either source or destination address space Id must point
    // to OT internal address space, but the memory range restriction does not apply if _both_
    // are within the OT internal address space.
    if (src_asid == OtInternalAddr && dst_asid != OtInternalAddr) begin
      if (mem_range_valid && !is_buffer_in_dma_memory_region(src_addr[31:0], memory_range)) begin
        // If source address space ID points to OT internal address space,
        // it must be within DMA enabled address range.
        `uvm_info(`gfn,
                $sformatf(
                  " - Invalid src addr range found lo: %08x hi: %08x with base: %08x limit: %0x",
                  src_addr[31:0], src_addr[63:32], mem_range_base, mem_range_limit),
                UVM_MEDIUM)
        valid_config = 0;
      end
    end else if (dst_asid == OtInternalAddr && src_asid != OtInternalAddr) begin
      // If destination address space ID points to OT internal address space
      // it must be within DMA enabled address range.
      if (mem_range_valid && !is_buffer_in_dma_memory_region(dst_addr[31:0], memory_range)) begin
        `uvm_info(`gfn,
                  $sformatf(
                    " - Invalid dst addr range found lo: %08x hi: %08x with base: %08x limit: %0x",
                    dst_addr[31:0], dst_addr[63:32], mem_range_base, mem_range_limit),
                  UVM_MEDIUM)
        valid_config = 0;
      end
    end

    // Check that the upper 32 bits of the destination and source address are zero for
    // 32-bit address spaces
    if (dst_asid != SocSystemAddr && |dst_addr[63:32]) begin
      `uvm_info(`gfn, " - Destination address out of range for destination ASID", UVM_MEDIUM)
      valid_config = 0;
    end
    if (src_asid != SocSystemAddr && |src_addr[63:32]) begin
      `uvm_info(`gfn, " - Source addess out of range for source ASID", UVM_MEDIUM)
      valid_config = 0;
    end

    // Source and destination addresses must meet alignment requirements
    case (per_transfer_width)
      DmaXfer1BperTxn: align_mask = 2'b00;
      DmaXfer2BperTxn: align_mask = 2'b01;
      DmaXfer4BperTxn: align_mask = 2'b11;
      default: begin
        align_mask = 2'b00;
        `uvm_info(`gfn, " - Invalid transfer width", UVM_MEDIUM)
        valid_config = 0;
      end
    endcase

    if (|(src_addr & align_mask)) begin
      `uvm_info(`gfn, " - Source address does not meet alignment requirements", UVM_MEDIUM)
      valid_config = 0;
    end
    if (|(dst_addr & align_mask)) begin
      `uvm_info(`gfn, " - Destination address does not meet alignment requirements", UVM_MEDIUM)
      valid_config = 0;
    end

    // Multi-chunk transfers will fault the transfer at the point of starting non-initial chunks
    // if the `chunk_data_size` values does not ensure that they do not have appropriately-aligned
    // addresses, so we expect an error at some point even if not immediately.
    if (chunk_data_size < total_data_size && (!handshake || auto_inc_buffer)) begin
      if (|(chunk_data_size & align_mask)) begin
        `uvm_info(`gfn,
                  " - Chunk data does not meet alignment requirements for multi-chunk transfers",
                  UVM_MEDIUM)
      end
    end

    if (valid_config) begin
      `uvm_info(`gfn, "=> Configuration accepted as valid", UVM_MEDIUM)
    end else begin
      `uvm_info(`gfn, "=> Configuration is invalid", UVM_MEDIUM)
    end
    return valid_config;
  endfunction: check_config

  // Method to convert transfer width to a corresponding value for the a_size field
  static function uint transfer_width_to_a_size(dma_transfer_width_e width);
    case (width)
      DmaXfer1BperTxn: return 0;
      DmaXfer2BperTxn: return 1;
      default:         return 2;
    endcase
  endfunction

  // Method to convert transfer_width enum to number of bytes per transaction
  static function uint transfer_width_to_num_bytes(dma_transfer_width_e width);
    case (width)
      DmaXfer1BperTxn: return 1;
      DmaXfer2BperTxn: return 2;
      default:         return 4;
    endcase
  endfunction

  // Method to return the value for the a_size field for this object
  function uint a_size();
    `DV_CHECK(per_transfer_width inside {DmaXfer1BperTxn, DmaXfer2BperTxn, DmaXfer4BperTxn},
              $sformatf("Unexpected transfer width %d", per_transfer_width))
    return transfer_width_to_a_size(per_transfer_width);
  endfunction

  // Method to return the bytes per transaction for this object
  function uint txn_bytes();
    `DV_CHECK(per_transfer_width inside {DmaXfer1BperTxn, DmaXfer2BperTxn, DmaXfer4BperTxn},
              $sformatf("Unexpected transfer width %d", per_transfer_width))
    return transfer_width_to_num_bytes(per_transfer_width);
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
    total_data_size = 0;
    per_transfer_width = DmaXfer1BperTxn;
    auto_inc_buffer = 0;
    auto_inc_fifo = 0;
    handshake = 0;
    // reset non random variables
    valid_dma_config = 0;
    range_regwen = MuBi4True;
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
    total_data_size.rand_mode(0);
    per_transfer_width.rand_mode(0);
    auto_inc_buffer.rand_mode(0);
    auto_inc_fifo.rand_mode(0);
    handshake.rand_mode(0);
    range_regwen.rand_mode(0);
  endfunction

  // Return if Read FIFO mode enabled (no auto increment of source address)
  function bit get_read_fifo_en();
    return handshake && // Handshake mode enabled
           direction == DmaRcvData && // Read from FIFO
           !auto_inc_fifo; // FIFO address auto increment disabled
  endfunction

  // Return if Write FIFO mode enabled (no auto increment of destination address)
  function bit get_write_fifo_en();
    return handshake && // Handshake mode enabled
           direction == DmaSendData && // Write to FIFO
           !auto_inc_fifo; // FIFO address auto increment disabled
  endfunction

  // Function to indicate a register write is expected from DMA
  // to clear LSIO interrupt
  function bit get_lsio_intr_clear();
    return (handshake_intr_en && clear_intr_src);
  endfunction

  // Simply utility function that returns the actual size of a chunk starting at the given offset
  function bit [31:0] chunk_size(bit [31:0] offset);
    if (offset < total_data_size) begin
      bit [31:0] bytes_left = total_data_size - offset;
      return (chunk_data_size < bytes_left) ? chunk_data_size : bytes_left;
    end else begin
      return 32'b0;
    end
  endfunction

endclass : dma_seq_item
