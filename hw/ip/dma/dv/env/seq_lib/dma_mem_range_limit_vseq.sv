// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Directed sequence for the inclusive ENABLED_MEMORY_RANGE_LIMIT. Each transaction places the OT
// side of an import or export at the limit boundary, sweeping every direction, transfer width and
// boundary case once:
// - the final byte lies exactly at the limit (accepted);
// - the final byte lies at limit + 1 (rejected);
// - the limit is 0xFFFF_FFFF and the final byte lies exactly at it (accepted);
// - the limit is 0xFFFF_FFFF and the transfer wraps past the 32-bit space (rejected).

class dma_mem_range_limit_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_mem_range_limit_vseq)
  `uvm_object_new

  typedef enum {
    LastByteAtLimit,
    LastBytePastLimit,
    TopEndAtLimit,
    TopEndWrap
  } limit_case_e;

  // One transaction for each direction x transfer width x boundary case.
  constraint iters_c {num_iters == 1;}
  constraint transactions_c {num_txns == 2 * 3 * 4;}

  // Index of the next boundary configuration.
  uint case_idx;

  // Half of the configurations are deliberately rejected.
  virtual function bit pick_if_config_valid();
    return 1'b0;
  endfunction

  virtual function void randomize_item(ref dma_seq_item dma_config);
    bit ot_is_src = case_idx[0];
    dma_transfer_width_e width = dma_transfer_width_e'((case_idx / 2) % 3);
    limit_case_e kind = limit_case_e'((case_idx / 6) % 4);
    uint txn_bytes = dma_seq_item::transfer_width_to_num_bytes(width);
    // At least two transactions, so that the limit check rather than the start check decides.
    bit [31:0] size = txn_bytes * $urandom_range(2, 8);
    bit [31:0] align_mask = ~(txn_bytes - 1);
    bit [31:0] base, limit;
    bit [63:0] ot_addr;
    bit [63:0] soc_addr = $urandom_range(32'h1000, 32'h7FFF_0000) & align_mask;
    bit exp_valid;

    case_idx++;
    case (kind)
      LastByteAtLimit, LastBytePastLimit: begin
        ot_addr = $urandom_range(32'h1000, 32'h7FFF_0000) & align_mask;
        base    = ot_addr[31:0] & ~32'hFFF;
        limit   = ot_addr[31:0] + size - ((kind == LastByteAtLimit) ? 1 : 2);
      end
      TopEndAtLimit: begin
        ot_addr = 64'h1_0000_0000 - size;
        base    = 32'h8000_0000;
        limit   = 32'hFFFF_FFFF;
      end
      default: begin  // TopEndWrap
        ot_addr = 64'h1_0000_0000 - size + txn_bytes * $urandom_range(1, size / txn_bytes - 1);
        base    = 32'h8000_0000;
        limit   = 32'hFFFF_FFFF;
      end
    endcase
    exp_valid = kind inside {LastByteAtLimit, TopEndAtLimit};

    `uvm_info(`gfn, $sformatf("Limit case %s: ot_is_src %0d width %s addr 0x%0x size 0x%0x",
                              kind.name(), ot_is_src, width.name(), ot_addr, size), UVM_LOW)

    // Single-chunk transfers, so that the range check covers the whole buffer.
    dma_config.multi_chunk_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      dma_config,
      src_asid == (local::ot_is_src ? OtInternalAddr : SocControlAddr);
      dst_asid == (local::ot_is_src ? SocControlAddr : OtInternalAddr);
      src_addr == (local::ot_is_src ? local::ot_addr : local::soc_addr);
      dst_addr == (local::ot_is_src ? local::soc_addr : local::ot_addr);
      per_transfer_width == local::width;
      total_data_size == local::size;
      chunk_data_size == local::size;
      opcode == OpcCopy;
      handshake == 1'b0;
      src_addr_inc == 1'b1;
      dst_addr_inc == 1'b1;
      src_chunk_wrap == 1'b0;
      dst_chunk_wrap == 1'b0;
      mem_range_valid == 1'b1;
      mem_range_base == local::base;
      mem_range_limit == local::limit;)
    dma_config.multi_chunk_c.constraint_mode(1);
    // The scoreboard predicts the outcome from this model, so it must agree with the case.
    `DV_CHECK_EQ(dma_config.is_valid_config, exp_valid)
  endfunction

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting mem range limit Sequence", UVM_LOW)
    super.body();
    `uvm_info(`gfn, "DMA: Completed mem range limit Sequence", UVM_LOW)
  endtask : body
endclass
