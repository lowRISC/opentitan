// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence is specifically to ensure the partial overlaps between the source/destination
// buffer and the DMA-enabled memory range are exercised, as well as regular 'fully contained'
// transfers.
// This DMA-enabled memory range is used only when importing to/exporting from the OT domain.

class dma_mem_enabled_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_mem_enabled_vseq)
  `uvm_object_new

  constraint iters_c {num_iters inside {[2:4]};}
  constraint transactions_c {num_txns == 16;}

  // Cannot constrain this sequence to valid configurations because we're specifically trying to
  // exercise out-of-range transfers.
  virtual function bit pick_if_config_valid();
    return 1'b0;
  endfunction

  // Randomization of DMA configuration and transfer properties; constraints are set to ensure that
  // the memory limit addresses shall be used, and we shall usually want them to be close to the
  // destination address range of the transfer because otherwise the 32- or 64-bit address range
  // is too large make collisions probable.
  virtual function void randomize_item(ref dma_seq_item dma_config);
    asid_encoding_e dst_chosen = OtInternalAddr;
    asid_encoding_e src_chosen;
    bit contained;
    // Decide whether we want the source/destination range to be contained within the DMA-enabled
    // memory range.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(contained, contained dist { 0 := 20, 1 := 80};)
    // Decide upon the direction of the data transfer.
    // TODO: presently we cannot employ SocSystemAddr, so we must use only the other two buses;
    //       otherwise randomization may fail.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(src_chosen,
                                       src_chosen inside {OtInternalAddr, SocControlAddr};)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(dst_chosen,
                                       dst_chosen inside {OtInternalAddr, SocControlAddr};)

    // Select the appropriate constraints for containment or partial overlap; source and destination
    // ranges are normally selected to lie within the DMA-enabled memory range when selecting a
    // valid DMA configuration.
    // Here we are randomly forcing one end of the transfer to be outside the DMA-enabled range.
    // Note also that the DMA-enabled range does not apply if both ends are in OtInternalAddr space.
    dma_config.src_addr_in_range = (src_chosen == OtInternalAddr) ? contained : 1'b1;
    dma_config.dst_addr_in_range = (src_chosen != OtInternalAddr) ? contained : 1'b1;

    `uvm_info(`gfn, $sformatf("src_asid 0x%0x dst_asid 0x%0x contained %d",
                              src_chosen, dst_chosen, contained), UVM_MEDIUM)

    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      dma_config,
      dst_asid == dst_chosen;
      src_asid == src_chosen;)
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_MEDIUM)
  endfunction

  // The functionality of this vseq is implemented in `dma_generic_vseq`
  virtual task body();
    `uvm_info(`gfn, "DMA: Starting mem enabled Sequence", UVM_LOW)
    super.body();
    `uvm_info(`gfn, "DMA: Completed mem enabled Sequence", UVM_LOW)
  endtask : body
endclass
