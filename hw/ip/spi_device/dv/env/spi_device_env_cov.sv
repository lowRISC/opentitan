// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class tpm_read_hw_reg_cg_wrap;
  covergroup tpm_read_hw_reg_cg (string name) with function sample(
      bit hit);
    option.per_instance = 1;
    option.name = name;

    cp_hit: coverpoint hit {
      bins done = {1};
    }
  endgroup

  function new(string name);
    tpm_read_hw_reg_cg = new(name);
  endfunction : new

  function void sample();
    tpm_read_hw_reg_cg.sample(1);
  endfunction : sample
endclass

class spi_device_env_cov extends cip_base_env_cov #(.CFG_T(spi_device_env_cfg));
  `uvm_component_utils(spi_device_env_cov)
  tpm_read_hw_reg_cg_wrap tpm_read_hw_reg_cg_wraps[string];

  // sample this spi mode when receive a transaction to ensure the mode is actually used.
  covergroup all_modes_cg with function sample(device_mode_e mode, bit tpm_enabled);
    cp_mode: coverpoint mode;
    cp_tpm_enabled: coverpoint tpm_enabled;
    cr_all: cross cp_mode, cp_tpm_enabled {
      // FW mode can't run with TPM enabled
      // but if we turn the mode on without realling sending transactions, it's fine.
      ignore_bins invalid = binsof(cp_mode) intersect { GenericMode } &&
                             binsof(cp_tpm_enabled) intersect { 1 };
    }
  endgroup

  covergroup bit_order_clk_cfg_cg with function sample(bit tx_order, bit rx_order,
                                                       bit cpol, bit cpha);
    cp_bit_order: coverpoint tx_order;
    cp_rx_order: coverpoint rx_order;
    cp_cpol: coverpoint cpol;
    cp_cpha: coverpoint cpha;
    cr_all: cross tx_order, rx_order, cp_cpol, cp_cpha;
  endgroup

  covergroup fw_tx_fifo_size_cg with function sample(int tx_size);
    cp_tx_size: coverpoint tx_size {
      bins sizes[5] = {[0:SRAM_SIZE]};
      bins specific_sizes[] = {SRAM_WORD_SIZE, SRAM_SIZE / 2, SRAM_SIZE - SRAM_WORD_SIZE};
    }
  endgroup

  covergroup fw_rx_fifo_size_cg with function sample(int rx_size);
    cp_rx_size: coverpoint rx_size {
      bins sizes[5] = {[0:SRAM_SIZE]};
      bins specific_sizes[] = {SRAM_WORD_SIZE, SRAM_SIZE / 2, SRAM_SIZE - SRAM_WORD_SIZE};
    }
  endgroup

  // TPM related
  covergroup tpm_cfg_cg with function sample(
      // CSR cfg
      tpm_cfg_mode_e tpm_mode, bit hw_reg_dis, bit tpm_reg_chk_dis, bit invalid_locality,
      // transaction related info
      bit is_write, bit is_in_tpm_region, bit is_valid_locality, bit is_hw_reg_offset,
      bit is_word_aligned);
    cp_tpm_mode:          coverpoint tpm_mode;
    cp_hw_reg_dis:        coverpoint hw_reg_dis;
    cp_tpm_reg_chk_dis:   coverpoint tpm_reg_chk_dis;
    cp_invalid_locality:  coverpoint invalid_locality;
    cp_is_write:          coverpoint is_write;
    cp_is_in_tpm_region:  coverpoint is_in_tpm_region;
    cp_is_valid_locality: coverpoint is_valid_locality;
    cp_is_hw_reg_offset:  coverpoint is_hw_reg_offset;
    cp_is_word_aligned:   coverpoint is_word_aligned;

    cr_all: cross cp_tpm_mode, cp_hw_reg_dis, cp_tpm_reg_chk_dis, cp_invalid_locality, cp_is_write,
        cp_is_in_tpm_region, cp_is_valid_locality, cp_is_hw_reg_offset, cp_is_word_aligned;
  endgroup

  covergroup tpm_transfer_size_cg with function sample(
      bit is_write, bit is_hw_return, int transfer_size);
    cp_is_write:      coverpoint is_write;
    cp_is_hw_return:  coverpoint is_hw_return;
    cp_transfer_size: coverpoint transfer_size {
      bins interest[] = {1, 4, MAX_SUPPORT_TPM_SIZE};
      bins others[4] = {[2:MAX_SUPPORT_TPM_SIZE-1]};
    }
    cr_all: cross cp_is_write, cp_is_hw_return, cp_transfer_size {
      illegal_bins invalid = binsof(cp_is_write) intersect { 1 } &&
                             binsof(cp_is_hw_return) intersect { 1 };
    }
  endgroup

  covergroup tpm_sts_cg with function sample(bit is_write, bit active, bit is_hw_return,
                                             int locality);
    cp_is_write: coverpoint is_write;
    cp_active:   coverpoint active;
    cp_locality: coverpoint locality {
      bins valid[] = {[0:MAX_TPM_LOCALITY-1]};
    }
    cp_is_hw_return: coverpoint is_hw_return;
    cr_all: cross cp_is_write, cp_active, cp_locality, cp_is_hw_return {
      illegal_bins invalid = binsof(cp_is_write) intersect { 1 } &&
                             binsof(cp_is_hw_return) intersect { 1 };
    }
  endgroup

  // flash/passthrough related
  covergroup flash_cmd_info_cg with function sample(
      bit is_flash, bit[7:0] opcode, bit is_write, spi_flash_addr_mode_e addr_mode,
      bit addr_swap_en, bit payload_swap_en, bit upload, bit busy, int dummy_cycles,
      bit num_lanes);
    cp_is_flash: coverpoint is_flash;
    cp_opcode: coverpoint opcode {
      bins internal_process_ops[]   = {`ALL_INTERNAL_PROCESS_CMDS};
    }
    cp_is_write:        coverpoint is_write {
      bins write = {1};
      bins read = {0};
    }
    cp_addr_mode:       coverpoint addr_mode;
    cp_addr_swap_en:    coverpoint addr_swap_en;
    cp_payload_swap_en: coverpoint payload_swap_en;
    cp_upload:          coverpoint upload;
    cp_busy:            coverpoint busy;
    cp_dummy_cycles:    coverpoint dummy_cycles {
      bins values[]   = {[0:8]};
    }
    cp_num_lanes: coverpoint num_lanes {
      bins valids[]   = {0, 1, 2, 4};
      illegal_bins others = default;
    }

    cr_modeXdirXaddrXswap: cross cp_is_flash, cp_is_write, cp_addr_mode, cp_addr_swap_en,
                                 cp_payload_swap_en {
      // > payload_swap_en only works with write data
      ignore_bins payload_swap_writes = binsof(cp_is_write.read) &&
                                        binsof(cp_payload_swap_en) intersect {1};
    }
    cr_modeXdummyXnum_lanes: cross cp_is_flash, cp_dummy_cycles, cp_num_lanes;
  endgroup

  covergroup passthrough_addr_swap_cg with function sample(
      bit addr_swap_en, bit[TL_DW-1:0] data, bit[TL_DW-1:0] mask);
    cp_addr_swap_en: coverpoint addr_swap_en;
    cp_data: coverpoint data {
      bins values[8] = {[0:$]};
    }
    cp_mask: coverpoint mask{
      bins values[8] = {[0:$]};
    }

    cr_all: cross cp_addr_swap_en, cp_data, cp_mask;
  endgroup

  covergroup passthrough_payload_swap_cg with function sample(
      bit payload_swap_en, bit[TL_DW-1:0] data, bit[TL_DW-1:0] mask);
    cp_payload_swap_en: coverpoint payload_swap_en;
    cp_data: coverpoint data {
      bins values[8]   = {[0:$]};
    }
    cp_mask: coverpoint mask{
      bins values[8]   = {[0:$]};
    }

    cr_all: cross cp_payload_swap_en, cp_data, cp_mask;
  endgroup

  covergroup passthrough_cmd_filter_cg with function sample(
      bit [7:0] opcode, bit filtered);
    cp_opcode:   coverpoint opcode;
    cp_filtered: coverpoint filtered;

    cr_all: cross cp_opcode, cp_filtered;
  endgroup

  covergroup flash_status_cg with function sample(
      bit [23:0] status, bit is_host_read,
      bit sw_read_while_csb_active);
    cp_busy_bit:                 coverpoint status[0];
    cp_wel_bit:                  coverpoint status[1];
    cp_other_status:             coverpoint status[23:2] {
      // reduce bins for other_status, as they're not specially handled,
      // so that, cross coverage can be hit easier.
      option.auto_bin_max = 8;
    }
    cp_is_host_read:             coverpoint is_host_read;
    cp_sw_read_while_csb_active: coverpoint sw_read_while_csb_active;

    cr_all_except_csb: cross cp_busy_bit, cp_wel_bit, cp_other_status, cp_is_host_read;
    cr_busyXwelXcsb: cross cp_busy_bit, cp_wel_bit, cp_sw_read_while_csb_active;
  endgroup

  covergroup flash_upload_payload_size_cg with function sample(
      bit is_write, int payload_size);
    cp_is_write: coverpoint is_write {
      bins write = {1};
      bins read = {0};
    }
    cp_payload_size: coverpoint payload_size {
      bins frequent_use_values[] = {[0:4], 256};
      bins excess_fifo           = {[257:$]};
    }
    cr_all: cross cp_is_write, cp_payload_size {
      // In upstream host seq_items, reads don't have a payload
      // - The read payload is captured in the upstream device seq_item.
      // - See read_size/payload_q.size() in spi_host_flash_seq.sv for the randomization
      //   constraints that create this.
      illegal_bins read_w_nonzero_payload = binsof(cp_is_write.read) &&
                                            !binsof(cp_payload_size) intersect {0};
    }
  endgroup

  // sample this when receiving a command while busy bit is set
  // the command will be blocked regardless of filter enabled or not
  covergroup flash_command_while_busy_set_cg with function sample(bit filtered);
    cp_filtered: coverpoint filtered;
  endgroup

  covergroup flash_read_commands_cg with function sample(
      bit [7:0] opcode, int dummy_cycles, bit filtered,
      int payload_size, int intercept_en);
    cp_opcode: coverpoint opcode {
      bins internal_process_ops[]   = {`ALL_INTERNAL_PROCESS_CMDS};
    }
    cp_filtered: coverpoint filtered;
    cp_payload_size: coverpoint payload_size {
      bins frequent_use_values[] = {[0:4], 256};
      bins excess_fifo           = {[257:$]};
    }
    cr_all: cross cp_opcode, cp_filtered, cp_payload_size;
  endgroup

  covergroup passthrough_mailbox_cg with function sample(
      bit [7:0] opcode, read_addr_size_type_e addr_type, bit filtered);
    cp_opcode: coverpoint opcode {
      bins read_ops[]   = {`ALL_READ_CMDS};
    }
    cp_addr_type: coverpoint addr_type;
    cp_filtered: coverpoint filtered;
    cr_all: cross cp_opcode, cp_addr_type, cp_filtered;
  endgroup

  covergroup flash_mailbox_cg with function sample(bit [7:0] opcode);
    cp_opcode: coverpoint opcode {
      bins read_ops[]   = {`ALL_READ_CMDS};
    }
  endgroup

  covergroup spi_device_addr_4b_enter_exit_command_cg with function sample(
      bit addr_4b_en, bit prev_addr_4b_en);
    cp_addr_4b_en: coverpoint addr_4b_en;
    cp_prev_addr_4b_en: coverpoint prev_addr_4b_en;
    cr_all: cross cp_addr_4b_en, cp_prev_addr_4b_en;
  endgroup

  covergroup sw_update_addr4b_cg with function sample(bit update = 1);
    cp_update: coverpoint update {
      bins done = {1};
    }
  endgroup

  covergroup spi_device_write_enable_disable_cg with function sample(
      bit wr_en, bit prev_wr_en);
    cp_wr_en: coverpoint wr_en;
    cp_prev_wr_en: coverpoint prev_wr_en;
    cr_all: cross cp_wr_en, cp_prev_wr_en;
  endgroup

  covergroup spi_device_buffer_boundary_cg with function sample(
      bit [7:0] opcode, bit flip_position);
    cp_opcode: coverpoint opcode {
      bins read_ops[]   = {`ALL_READ_CMDS};
    }
    cp_flip_position: coverpoint flip_position;
  endgroup

  covergroup tpm_interleave_with_flash_item_cg with function sample(
      bit is_tpm_item, bit is_flash_item);
    cp_interleave: coverpoint {is_tpm_item, is_flash_item} {
      bins tpm_flash_tpm   = (2'b10 => 2'b01 => 2'b10);
      bins flash_tpm_flash = (2'b01 => 2'b10 => 2'b01);
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // add more covergroup here
    foreach (ALL_TPM_HW_REG_NAMES[i]) begin
      tpm_read_hw_reg_cg_wraps[ALL_TPM_HW_REG_NAMES[i]] = new(ALL_TPM_HW_REG_NAMES[i]);
    end
    all_modes_cg = new();
    bit_order_clk_cfg_cg = new();
    fw_tx_fifo_size_cg = new();
    fw_rx_fifo_size_cg = new();
    // tpm
    tpm_cfg_cg = new();
    tpm_transfer_size_cg = new();
    tpm_sts_cg = new();
    // flash/passthrough
    flash_cmd_info_cg = new();
    passthrough_addr_swap_cg = new();
    passthrough_payload_swap_cg = new();
    passthrough_cmd_filter_cg = new();
    flash_status_cg = new();
    flash_upload_payload_size_cg = new();
    flash_command_while_busy_set_cg = new();
    flash_read_commands_cg = new();
    passthrough_mailbox_cg = new();
    flash_mailbox_cg = new();
    spi_device_addr_4b_enter_exit_command_cg = new();
    sw_update_addr4b_cg = new();
    spi_device_write_enable_disable_cg = new();
    spi_device_buffer_boundary_cg = new();
    tpm_interleave_with_flash_item_cg = new();
  endfunction : new

endclass
