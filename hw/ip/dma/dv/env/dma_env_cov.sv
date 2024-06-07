// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef DMA_ENV_COV_32B_ADDR_BINS
  `dv_fatal("Did not expect DMA_ENV_COV_32B_ADDR_BINS to be defined already!")
`else
  `define DMA_ENV_COV_32B_ADDR_BINS \
    bins zero = {'0}; \
    bins less_than_4_KiB = {[1:4095]}; \
    bins between_4_and_64_KiB = {[4096:64*1024-1]}; \
    bins between_64_KiB_and_1_GiB = {[64*1024:'h3fff_ffff]}; \
    bins between_1_and_4_GiB = {['h4000_0000:'hffff_ffff]};
`endif

`ifdef DMA_ENV_COV_64B_ADDR_BINS
  `dv_fatal("Did not expect DMA_ENV_COV_64B_ADDR_BINS to be defined already!")
`else
  `define DMA_ENV_COV_64B_ADDR_BINS \
    `DMA_ENV_COV_32B_ADDR_BINS \
    bins above_4_GiB = {['h1_0000_0000:$]};
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

  cp_opcode: coverpoint dma_config.opcode;

  cp_mem_range_base: coverpoint dma_config.mem_range_base {
    `DMA_ENV_COV_32B_ADDR_BINS
  }

  cp_mem_range_limit: coverpoint dma_config.mem_range_limit {
    `DMA_ENV_COV_32B_ADDR_BINS
  }

  cp_handshake: coverpoint dma_config.handshake;

  cp_data_direction: coverpoint dma_config.direction {
    bins read_from_fifo = {DmaRcvData};
    bins write_to_fifo = {DmaSendData};
  }

  cp_fifo_auto_inc: coverpoint dma_config.auto_inc_fifo;

  cp_mem_buffer_auto_inc: coverpoint dma_config.auto_inc_buffer;

  cp_handshake_intr: coverpoint dma_config.handshake_intr_en;

  cp_initial_transfer: coverpoint initial_transfer;

  cr_src_addr_X_src_asid: cross
      cp_src_addr,
      cp_src_asid;

  cr_dst_addr_X_dst_asid: cross
      cp_dst_addr,
      cp_dst_asid;

  cr_opcode_X_src_asid_X_dst_asid_X_handshake_X_data_direction: cross
      cp_opcode,
      cp_src_asid,
      cp_dst_asid,
      cp_handshake,
      cp_data_direction;

  cr_opcode_X_chunk_data_size_X_src_asid_X_dst_asid_X_data_direction: cross
      cp_opcode,
      cp_chunk_data_size,
      cp_src_asid,
      cp_dst_asid,
      cp_data_direction;

  cr_opcode_X_total_data_size_X_transfer_width_X_data_direction: cross
      cp_opcode,
      cp_total_data_size,
      cp_transfer_width,
      cp_data_direction;

  cr_opcode_X_handshake_X_chunk_data_size_X_transfer_width_X_data_direction: cross
      cp_opcode,
      cp_handshake,
      cp_chunk_data_size,
      cp_transfer_width,
      cp_data_direction;

  cr_opcode_X_handshake_X_mem_buffer_auto_inc_X_fifo_auto_inc_X_data_direction: cross
      cp_opcode,
      cp_handshake,
      cp_mem_buffer_auto_inc,
      cp_fifo_auto_inc,
      cp_data_direction;

  cr_opcode_X_handshake_X_data_direction_X_initial_transfer: cross
      cp_opcode,
      cp_handshake,
      cp_data_direction,
      cp_initial_transfer;

  cr_src_addr_X_dst_addr_X_mem_range_base_X_mem_range_limit_X_data_direction: cross
      cp_src_addr,
      cp_dst_addr,
      cp_mem_range_base,
      cp_mem_range_limit,
      cp_data_direction;

  cr_src_addr_alignment_X_dst_addr_alignment_X_total_data_size_alignment_X_transfer_width: cross
      cp_src_addr_alignment,
      cp_dst_addr_alignment,
      cp_total_data_size_alignment,
      cp_transfer_width;

endgroup

covergroup dma_tlul_error_cg with function sample(dma_seq_item dma_config,
                                                  asid_encoding_e tl_err_asid);
  option.per_instance = 1;
  option.name = "dma_tlul_error_cg";

  cp_tl_err_asid: coverpoint tl_err_asid;

  cr_tl_err_asid_X_src_asid_X_dst_asid_X_direction: cross
      cp_tl_err_asid,
      dma_config.src_asid,
      dma_config.dst_asid,
      dma_config.direction;

endgroup

covergroup dma_status_cg with function sample(
  bit busy,
  bit done,
  bit aborted,
  bit error,
  bit sha2_digest_valid
);
  option.per_instance = 1;
  option.name = "dma_status_cg";
  cp_status_busy: coverpoint busy;
  cp_status_done: coverpoint done;
  cp_status_aborted: coverpoint aborted;
  cp_status_error: coverpoint error;
  cp_sha2_digest_valid: coverpoint sha2_digest_valid;
endgroup

covergroup dma_error_code_cg with function sample(
  bit[7:0] error_code
);
  option.per_instance = 1;
  option.name = "dma_error_code_cg";

  cp_status_errcode: coverpoint error_code {
    bins error_code[] = {[0:$]};
  }
endgroup

covergroup dma_interrupt_cg with function sample(
  bit [dma_reg_pkg::NumIntClearSources-1:0] handshake_interrupt_enable,
  bit [dma_reg_pkg::NumIntClearSources-1:0] clear_intr_src,
  bit [dma_reg_pkg::NumIntClearSources-1:0] clear_intr_bus,
  bit [dma_reg_pkg::NumIntClearSources-1:0][2:0] intr_source_addr_offset,
  bit [dma_reg_pkg::NumIntClearSources-1:0][31:0] intr_source_wr_val
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

  cp_int_source_addr_offset: coverpoint intr_source_addr_offset {
    bins all_zero = {0};
    bins first_1_others_0 = {3'b001};
    bins first_2_others_0 = {3'b010};
    bins first_3_others_0 = {3'b011};
    bins first_4_others_0 = {3'b100};
    bins first_5_others_0 = {3'b101};
    bins first_6_others_0 = {3'b110};
    bins first_7_others_0 = {3'b111};
    bins second_1_others_0 = {6'b001000};
    bins second_2_others_0 = {6'b010000};
    bins second_3_others_0 = {6'b011000};
    bins second_4_others_0 = {6'b100000};
    bins second_5_others_0 = {6'b101000};
    bins second_6_others_0 = {6'b110000};
    bins second_7_others_0 = {6'b111000};
    bins first_1_second_1_others_0 = {6'b001001};
    bins first_2_second_1_others_0 = {6'b001010};
    bins first_3_second_1_others_0 = {6'b001011};
    bins first_1_second_2_others_0 = {6'b010001};
    bins first_1_second_3_others_0 = {6'b011001};
    // TODO: There are other bins that would be relevant (but the autogenerated ones aren't).
    // Is there a way to programatically generate more enumerations like the above?
  }

  cp_int_source_wr_val: coverpoint intr_source_wr_val {
    bins all_zero = {0};
    bins first_all_ones_others_zero = {32'hffff_ffff};
    bins second_all_ones_others_zero = {64'hffff_ffff_0000_0000};
    // TODO: There are other bins that bins that would be relevant but enumerating them is
    // infeasible, and `with` bins expressions such as the following
    //     bins first_non_zero = {[0:$]} with (item & 32'hffff_ffff != 0);
    //     bins second_non_zero = {[0:$]} with ((item >> 32) & 32'hffff_ffff != 0);
    // increase the runtime so significantly that even simple tests take a prohibitively long time
    // to complete.  What is another way to specify more of the interesting bins?
  }

endgroup

class dma_env_cov extends cip_base_env_cov #(.CFG_T(dma_env_cfg));
  `uvm_component_utils(dma_env_cov)

  dma_config_cg config_cg;
  dma_tlul_error_cg tlul_error_cg;
  dma_status_cg status_cg;
  dma_error_code_cg error_code_cg;
  dma_interrupt_cg interrupt_cg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    config_cg = new();
    tlul_error_cg = new();
    status_cg = new();
    error_code_cg = new();
    interrupt_cg = new();
  endfunction: new

endclass
