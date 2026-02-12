// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef DMA_ENV_COV_32B_ADDR_BINS
  `dv_fatal("Did not expect DMA_ENV_COV_32B_ADDR_BINS to be defined already!")
`else
  `define DMA_ENV_COV_32B_ADDR_BINS \
    bins less_than_1MiB = {[0:'hf_ffff]}; \
    bins between_1MiB_and_2_GiB = {['h10_0000:'h7fff_ffff]}; \
    bins between_2_and_4_GiB = {['h8000_0000:'hffff_ffff]};
`endif

`ifdef DMA_ENV_COV_64B_ADDR_BINS
  `dv_fatal("Did not expect DMA_ENV_COV_64B_ADDR_BINS to be defined already!")
`else
  `define DMA_ENV_COV_64B_ADDR_BINS \
    `DMA_ENV_COV_32B_ADDR_BINS \
    bins above_4_GiB = {['h1_0000_0000:'h7fff_ffff_ffff_ffff]}; \
    bins msb_set = {['h8000_0000_0000_0000:$]};
`endif

`ifdef DMA_ENV_COV_SIZE_BINS \
  `dv_fatal("Did not expect DMA_ENV_COV_SIZE_BINS to be defined already!")
`else
  `define DMA_ENV_COV_SIZE_BINS \
    bins one_byte = {1}; \
    bins two_byte = {2}; \
    bins three_byte = {3}; \
    bins four_byte = {4}; \
    bins between_5_and_15_byte = {[5:15]}; \
    bins between_16_and_127_byte = {[16:127]}; \
    bins between_128_and_1023_byte = {[128:1023]}; \
    bins kibi_byte = {[1024:1024*1024-1]}; \
    bins mebi_byte = {[1024*1024:1024*1024*1024-1]}; \
    bins gibi_byte = {[1024*1024*1024:$]};
`endif

`ifdef DMA_ENV_COV_INTERRUPT_BINS
  `dv_fatal("Did not expect DMA_ENV_COV_INTERRUPT_BINS to be defined already!")
`else
  `define DMA_ENV_COV_INTERRUPT_BINS \
    bins none_enabled = {0}; \
    bins one_enabled[] = {[0:$]} with ($onehot(item)); \
    bins two_enabled[] = {[0:$]} with ($countones(item) == 2); \
    bins all_enabled = {'1};
`endif

covergroup dma_config_cg with function sample(dma_seq_item dma_config,
                                              bit initial_transfer);
  option.per_instance = 1;
  option.name = "dma_config_cg";

  cp_src_addr: coverpoint dma_config.src_addr {
    `DMA_ENV_COV_64B_ADDR_BINS
  }

  cp_src_addr_alignment: coverpoint shortint'(dma_config.src_addr % 8) {
    bins offset[] = {[0:7]};
  }

  cp_dst_addr: coverpoint dma_config.dst_addr {
    `DMA_ENV_COV_64B_ADDR_BINS
  }

  cp_dst_addr_alignment: coverpoint shortint'(dma_config.dst_addr % 8) {
    bins offset[] = {[0:7]};
  }

  cp_src_asid: coverpoint dma_config.src_asid;

  cp_dst_asid: coverpoint dma_config.dst_asid;

  cp_total_data_size: coverpoint dma_config.total_data_size {
    `DMA_ENV_COV_SIZE_BINS
  }

  cp_total_data_size_alignment: coverpoint shortint'(dma_config.total_data_size % 8) {
    bins offset[] = {[0:7]};
  }

  cp_chunk_data_size: coverpoint dma_config.chunk_data_size {
    `DMA_ENV_COV_SIZE_BINS
  }

  cp_transfer_width: coverpoint dma_config.per_transfer_width;

  cp_mem_range_base: coverpoint dma_config.mem_range_base {
    `DMA_ENV_COV_32B_ADDR_BINS
  }

  cp_mem_range_limit: coverpoint dma_config.mem_range_limit {
    `DMA_ENV_COV_32B_ADDR_BINS
  }

  cp_handshake: coverpoint dma_config.handshake;

  cp_dst_chunk_wrap: coverpoint dma_config.dst_chunk_wrap;

  cp_dst_addr_inc: coverpoint dma_config.dst_addr_inc;

  cp_src_chunk_wrap: coverpoint dma_config.src_chunk_wrap;

  cp_src_addr_inc: coverpoint dma_config.src_addr_inc;

  cp_handshake_intr: coverpoint dma_config.handshake_intr_en;

  cp_initial_transfer: coverpoint initial_transfer;

  cp_opcode: coverpoint dma_config.opcode;

  cr_src_addr_X_src_asid: cross
      cp_src_addr,
      cp_src_asid;

  cr_dst_addr_X_dst_asid: cross
      cp_dst_addr,
      cp_dst_asid;

  cr_src_asid_X_dst_asid_X_handshake: cross
      cp_src_asid,
      cp_dst_asid,
      cp_handshake;

  cr_chunk_data_size_X_src_asid_X_dst_asid: cross
      cp_chunk_data_size,
      cp_src_asid,
      cp_dst_asid;

  cr_total_data_size_X_transfer_width: cross
      cp_total_data_size,
      cp_transfer_width;

  cr_handshake_X_transfer_width_X_src_asid_X_dst_asid: cross
      cp_handshake,
      cp_transfer_width,
      cp_src_asid,
      cp_dst_asid;

  cr_handshake_X_dst_addr_inc_X_dst_chunk_wrap_X_src_addr_inc_X_src_chunk_wrap: cross
      cp_handshake,
      cp_dst_chunk_wrap,
      cp_dst_addr_inc,
      cp_src_chunk_wrap,
      cp_src_addr_inc;

  cr_handshake_X_initial_transfer: cross
      cp_handshake,
      cp_initial_transfer;

  cr_src_addr_X_dst_addr_X_mem_range_base_X_mem_range_limit: cross
      cp_src_addr,
      cp_dst_addr,
      cp_mem_range_base,
      cp_mem_range_limit;

  cr_src_addr_alignment_X_dst_addr_alignment_X_total_data_size_alignment_X_transfer_width: cross
      cp_src_addr_alignment,
      cp_dst_addr_alignment,
      cp_total_data_size_alignment,
      cp_transfer_width;

endgroup

// Ensure that we've seen a TL-UL error response from each address space (ASID) as both source
// (Reads) and destination (Writes).
covergroup dma_tlul_error_cg with function sample(asid_encoding_e tl_err_asid, bit is_source);
  option.per_instance = 1;
  option.name = "dma_tlul_error_cg";

  cp_tl_err_asid: coverpoint tl_err_asid;

  cp_tl_err_src: coverpoint is_source;

  cr_tl_err_asid_X_is_source: cross
      cp_tl_err_asid,
      cp_tl_err_src;

endgroup

covergroup dma_status_cg with function sample(
  bit busy,
  bit done,
  bit chunk_done,
  bit aborted,
  bit error,
  bit sha2_digest_valid
);
  option.per_instance = 1;
  option.name = "dma_status_cg";
  cp_status_busy: coverpoint busy;
  cp_status_done: coverpoint done;
  cp_status_chunk_done: coverpoint chunk_done;
  cp_status_aborted: coverpoint aborted;
  cp_status_error: coverpoint error;
  cp_sha2_digest_valid: coverpoint sha2_digest_valid;
endgroup

covergroup dma_error_code_cg with function sample(
  bit[7:0] error_code,
  asid_encoding_e asid,
  bit src
);
  option.per_instance = 1;
  option.name = "dma_error_code_cg";

  // Each configuration error is tested independently; there is no
  // benefit in trying to induce all permutations.
  cp_src_error: coverpoint error_code[DmaSrcAddrErr];
  cp_dst_error: coverpoint error_code[DmaDstAddrErr];
  cp_opc_error: coverpoint error_code[DmaOpcodeErr];
  cp_size_error: coverpoint error_code[DmaSizeErr];
  cp_asid_error: coverpoint error_code[DmaAsidErr];
  cp_baselim_error: coverpoint error_code[DmaBaseLimitErr];
  cp_rangeval_error: coverpoint error_code[DmaRangeValidErr];

  // For a bus error to be detected, the configuration must have been
  // accepted; i.e. the other errors shall not have been seen.
  cp_bus_error: coverpoint error_code[DmaBusErr];

  cp_src_dst: coverpoint src {
    bins src = {1};
    bins dst = {0};
  }

  cp_asid: coverpoint asid {
    bins OtInt = {OtInternalAddr};
    bins SocCnt = {SocControlAddr};
    bins SocSys = {SocSystemAddr};
  }

  // We want to observe both error and non-error responses on all ports.
  cr_asid_X_src_dst_X_bus_err: cross
    cp_asid,
    cp_src_dst,
    cp_bus_error;

  // We want to observe source address checking on all ports.
  cr_asid_X_src_error: cross
    cp_asid,
    cp_src_error;

  // We want to observe destination address checking on all ports.
  cr_asid_X_dst_error: cross
    cp_asid,
    cp_dst_error;

endgroup

// Interrupt-related configuration used in hardware-handshaking mode.
covergroup dma_interrupt_cg with function sample(
  bit [dma_reg_pkg::NumIntClearSources-1:0] handshake_interrupt_enable,
  bit [dma_reg_pkg::NumIntClearSources-1:0] clear_intr_src,
  bit [dma_reg_pkg::NumIntClearSources-1:0] clear_intr_bus
);
  option.per_instance = 1;
  option.name = "dma_interrupt_cg";

  cp_handshake_interrupt_enable: coverpoint handshake_interrupt_enable {
    `DMA_ENV_COV_INTERRUPT_BINS
  }

  cp_clear_intr_src: coverpoint clear_intr_src {
    `DMA_ENV_COV_INTERRUPT_BINS
  }

  cp_clear_intr_bus: coverpoint clear_intr_bus {
    `DMA_ENV_COV_INTERRUPT_BINS
  }

endgroup

// Interrupt-clearing address and data.
// - addresses are always word-aligned; there are no write strobes programmed.
covergroup dma_intr_src_cg with function sample(
  bit [top_pkg::TL_AW-1:0] intr_src_addr,
  bit [top_pkg::TL_DW-1:0] intr_src_data
);

  option.per_instance = 1;
  option.name = "dma_intr_src_cg";

  cp_intr_src_addr_alignment: coverpoint shortint'(intr_src_addr[3:2]) {
    bins offset[] = {[0:3]};
  }

  cp_intr_src_msb: coverpoint intr_src_addr[31] {
    bins clear = {0};
    bins set   = {1};
  }

  cp_int_source_wr_val: coverpoint |intr_src_data {
    bins all_zero = {0};
    bins non_zero = {1};
  }

endgroup

class dma_env_cov extends cip_base_env_cov #(.CFG_T(dma_env_cfg));
  `uvm_component_utils(dma_env_cov)

  dma_config_cg config_cg;
  dma_tlul_error_cg tlul_error_cg;
  dma_status_cg status_cg;
  dma_error_code_cg error_code_cg;
  dma_interrupt_cg interrupt_cg;
  dma_intr_src_cg intr_src_cg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    config_cg = new();
    tlul_error_cg = new();
    status_cg = new();
    error_code_cg = new();
    interrupt_cg = new();
    intr_src_cg = new();
  endfunction: new

endclass
