// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// DMA Configuration Coverage
covergroup dma_config_cg with function sample(dma_seq_item dma_config,
                                              bit abort,
                                              bit write_to_dma_mem_register,
                                              bit tl_src_err,
                                              bit tl_dst_err);
  option.per_instance = 1;
  option.name = "dma_config_cg";
  option.auto_bin_max = 8;
  // Source start address coverpoint
  cp_src_addr: coverpoint dma_config.src_addr;
  // Destination start address coverpoint
  cp_dst_addr: coverpoint dma_config.dst_addr;
  // Source address space ID
  cp_src_asid: coverpoint dma_config.src_asid;
  // Destination address space ID
  cp_dst_asid: coverpoint dma_config.dst_asid;
  // Total transfer size for operation
  cp_total_data_size: coverpoint dma_config.total_data_size {
    bins one_byte = {1};
    bins two_byte = {2};
    bins three_byte = {3};
    bins four_byte = {4};
    bins between_5_and_15_byte = {[5:15]};
    bins between_16_and_127_byte = {[16:127]};
    bins between_128_and_1023_byte = {[128:1023]};
    bins kibi_byte = {[1024:1024*1024-1]};
    bins mebi_byte = {[1024*1024:1024*1024*1024-1]};
    bins gibi_byte = {[1024*1024*1024:$]};
  }
  // Width of each transfer
  cp_transfer_width: coverpoint dma_config.per_transfer_width;
  // Cross of transfer width and total transfer size
  cp_transfer_width_x_transfer_size: cross cp_transfer_width, cp_total_data_size;
  // Opcode
  cp_opcode: coverpoint dma_config.opcode;
  // DMA enabled memory range base coverpoint
  cp_dma_mem_base: coverpoint dma_config.mem_range_base;
  // DMA enabled memory range limit coverpoint
  cp_dma_mem_range_limit: coverpoint dma_config.mem_range_limit;
  // Destination address limit coverpoint
  cp_dst_addr_limit: coverpoint dma_config.dst_addr_limit;
  // Destination address almost limit coverpoint
  cp_dst_addr_almost_limit: coverpoint dma_config.dst_addr_almost_limit;
  // handshake mode enable
  cp_handshake_mode: coverpoint dma_config.handshake;
  // data direction
  cp_data_direction: coverpoint dma_config.direction{
    bins read_from_fifo = {DmaRcvData};
    bins write_to_fifo = {DmaSendData};
  }
  cp_fifo_auto_inc: coverpoint dma_config.auto_inc_fifo;
  cp_mem_buffer_auto_inc: coverpoint dma_config.auto_inc_buffer;
  // Handshake mode FIFO enable coverpoint
  cp_handshake_fifo_mode: cross cp_data_direction, cp_fifo_auto_inc, cp_mem_buffer_auto_inc{
    bins read_src_inc_addr = binsof(cp_data_direction.read_from_fifo) &&
                             (binsof(cp_fifo_auto_inc) intersect {1});
    bins read_src_fixed_addr = binsof(cp_data_direction.read_from_fifo) &&
                               (binsof(cp_fifo_auto_inc) intersect {0});
    bins write_src_inc_addr = binsof(cp_data_direction.write_to_fifo) &&
                              (binsof(cp_mem_buffer_auto_inc) intersect {1});
    bins write_src_fixed_addr = binsof(cp_data_direction.write_to_fifo) &&
                                (binsof(cp_mem_buffer_auto_inc) intersect {0});
  }
  // DMA enabled memory range REGWEN
  cp_range_regwen: coverpoint dma_config.range_regwen{
    bins unlocked = {MuBi4True};
    bins locked = {MuBi4False};
// TODO: this faults with vcs
//  bins reserved = {[0:$]} with (!(item inside {MuBi4True, MuBi4False}));
  }
  // handhshake interrupt enable
  cp_handshake_intr: coverpoint dma_config.handshake_intr_en;
  // Abort via write to CONTROL
  cp_abort: coverpoint abort;
  // Cross OP code, source_address_space_id, destination_space_id and handshake mode
  cp_op_code_x_asid_x_handshake: cross cp_opcode, cp_src_asid, cp_dst_asid, cp_handshake_mode;
  cp_total_data_size_x_src_asid_x_dma_op: cross cp_transfer_width, cp_src_asid, cp_opcode;
  cp_transfer_width_x_dst_asid_x_dma_op: cross cp_transfer_width, cp_dst_asid, cp_opcode;
  cp_src_addr_x_src_asid_x_dma_op: cross cp_src_addr, cp_src_asid, cp_opcode;
  cp_dst_addr_x_dst_asid_x_dma_op: cross cp_dst_addr, cp_dst_asid, cp_opcode;
  cp_dma_mem_base_x_dma_mem_limit_x_dma_op: cross cp_dma_mem_base, cp_dma_mem_range_limit,
                                                  cp_opcode;
  cp_range_regwen_x_write_to_dma_mem_region_x_dma_op: cross cp_range_regwen,
                                                            write_to_dma_mem_register, cp_opcode;
  // Coverpoint for TL error on source interface
  cp_src_tl_err: coverpoint dma_config.src_asid iff (tl_src_err);

  // Coverpoint for TL error on destination interface
  cp_dst_tl_err: coverpoint dma_config.dst_asid iff (tl_dst_err);

  cp_src_asid_x_tl_src_err_x_dma_op: cross cp_src_asid, cp_src_tl_err, cp_opcode;

  cp_dst_asid_x_tl_dst_err_x_dma_op: cross cp_dst_asid, cp_dst_tl_err, cp_opcode;

  // Cross Destination address, memory buffer limit (if memory_buffer_auto_increment is set)
  cp_dst_addr_x_dst_addr_limit: cross cp_dst_addr,
                                      cp_dst_addr_limit
                                      iff (dma_config.auto_inc_buffer);

  // Cross Destination address, memory buffer threshold (if memory_buffer_auto_increment is set)
  cp_dst_addr_x_dst_addr_almost_limit: cross cp_dst_addr,
                                             cp_dst_addr_almost_limit
                                             iff (dma_config.auto_inc_buffer);

  cp_fifo_enable: cross cp_fifo_auto_inc, cp_mem_buffer_auto_inc, cp_data_direction;

  cp_fifo_enable_x_auto_inc: cross cp_fifo_enable,
                                   cp_mem_buffer_auto_inc iff(dma_config.handshake);

  cp_data_direction_x_asid: cross cp_src_asid,
                                  cp_dst_asid, cp_handshake_fifo_mode iff(dma_config.handshake);

  cp_data_direction_x_src_asid_x_fifo_auto_incr: cross cp_handshake_fifo_mode,
                                                       cp_src_asid iff (dma_config.handshake);

  // Cross data_direction, destination_address_space_id and memory_buffer_auto_increment_enable
  cp_data_direction_x_dst_asid_x_mem_buf_auto_incr: cross cp_handshake_fifo_mode,
                                                          cp_dst_asid iff (dma_config.handshake);
endgroup

// DMA Status Coverage
covergroup dma_status_cg with function sample(
  bit busy,
  bit done,
  bit aborted,
  bit error
);
  option.per_instance = 1;
  option.name = "dma_status_cg";
  cp_status_busy: coverpoint busy;
  cp_status_done: coverpoint done;
  cp_status_aborted: coverpoint aborted;
  cp_status_error: coverpoint error;
endgroup

covergroup dma_error_code_cg with function sample(
  bit[7:0] error_code
);
  option.per_instance = 1;
  option.name = "dma_error_code_cg";
  cp_status_errcode: coverpoint error_code;
endgroup

class dma_env_cov extends cip_base_env_cov #(.CFG_T(dma_env_cfg));
  `uvm_component_utils(dma_env_cov)

  dma_config_cg config_cg;
  dma_status_cg status_cg;
  dma_error_code_cg error_code_cg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    config_cg = new();
    status_cg = new();
    error_code_cg = new();
  endfunction: new

endclass
