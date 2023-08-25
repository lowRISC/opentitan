// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO checks for valid configurations
// Check if DMA memory range register lock is set
// Transaction checks
//   - Check a_size on each req item of source and destination interface
//   - Check data size requested on each item using a_mask
//   - Check address on each req item of source and destination interface
//   - Compare data between received data item from source interface and source memory model
//     (model data updated from sequence)
//   - Compare data between received data item from destination interface and destination
//     memory model(model data updated from sequence)
//   - Check if same data is observed on source and destination interfaces
//   - After end of operation check if all the addresses in the source and destination
//     address regions are covered

class dma_scoreboard extends cip_base_scoreboard #(
  .CFG_T(dma_env_cfg),
  .RAL_T(dma_reg_block),
  .COV_T(dma_env_cov)
);
  `uvm_component_utils(dma_scoreboard)

  `uvm_component_new

  // Internal variables to compare transactions
  dma_seq_item dma_config;

  // Indicates if DMA operation is in progress
  bit operation_in_progress;
  // Indicates if current DMA operation is valid or invalid
  bit current_operation_valid = 1;
  // Variable to keep track of number of bytes transferred in current operation
  uint num_bytes_transfered;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create a_channel analysis fifo
    foreach (cfg.dma_a_fifo[key]) begin
      tl_a_chan_fifos[cfg.dma_a_fifo[key]] = new(cfg.dma_a_fifo[key], this);
    end
    foreach (cfg.dma_d_fifo[key]) begin
      tl_d_chan_fifos[cfg.dma_d_fifo[key]] = new(cfg.dma_d_fifo[key], this);
    end
    foreach (cfg.dma_dir_fifo[key]) begin
      tl_dir_fifos[cfg.dma_dir_fifo[key]] = new(cfg.dma_dir_fifo[key], this);
    end
    dma_config = dma_seq_item::type_id::create("dma_config");

  endfunction: build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      process_host_fifo();
      process_ctn_fifo();
      process_csr_fifo();
      //process_tl_access();
    join
  endtask

  virtual task process_host_fifo();
  endtask

  virtual task process_ctn_fifo();
  endtask

  virtual task process_csr_fifo();
  endtask

  // Method to process DMA register write
  function void process_reg_write(tl_seq_item item, uvm_reg csr);
    `uvm_info(`gfn, $sformatf("Got reg_write to %s with addr : %0x and data : %0x ",
                              csr.get_name(), item.a_addr, item.a_data), UVM_HIGH)
    // incoming access is a write to a valid csr, so make updates right away
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

    case (csr.get_name())
      "source_address_lo": begin
        dma_config.src_addr[31:0] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got source_address_lo = %0x",
                                  dma_config.src_addr[31:0]), UVM_HIGH)
      end
      "source_address_hi": begin
        dma_config.src_addr[63:32] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got source_address_hi = %0x",
                                  dma_config.src_addr[63:32]), UVM_HIGH)
      end
      "destination_address_lo": begin
        dma_config.dst_addr[31:0] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got destination_address_lo = %0x",
                                  dma_config.dst_addr[31:0]), UVM_HIGH)
      end
      "destination_address_hi": begin
        dma_config.dst_addr[63:32] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got destination_address_hi = %0x",
                                  dma_config.dst_addr[63:32]), UVM_HIGH)
      end
      "address_space_id": begin
        // Get mirrored field value and cast to associated enum in dma_config
        dma_config.src_asid = asid_encoding_e'(`gmv(ral.address_space_id.source_asid));
        `uvm_info(`gfn, $sformatf("Got source address space id : %s",
                                  dma_config.src_asid.name()), UVM_HIGH)
        // Get mirrored field value and cast to associated enum in dma_config
        dma_config.dst_asid = asid_encoding_e'(`gmv(ral.address_space_id.destination_asid));
        `uvm_info(`gfn, $sformatf("Got destination address space id : %s",
                                  dma_config.dst_asid.name()), UVM_HIGH)
      end
      "enabled_memory_range_base": begin
        dma_config.mem_range_base = item.a_data;
        `uvm_info(`gfn, $sformatf("Got enabled_memory_range_base = %0x",
                                  dma_config.mem_range_base), UVM_HIGH)
      end
      "enabled_memory_range_limit": begin
        dma_config.mem_range_limit = item.a_data;
        `uvm_info(`gfn, $sformatf("Got enabled_memory_range_limit = %0x",
                                  dma_config.mem_range_limit), UVM_HIGH)
      end
      "range_unlock_regwen": begin
        // Get mirrored field value and cast to associated enum in dma_config
        dma_config.mem_range_unlock = mubi4_t'(`gmv(ral.range_unlock_regwen.unlock));
        `uvm_info(`gfn, $sformatf("Got range register unlock = %s",
                                  dma_config.mem_range_unlock.name()), UVM_HIGH)
      end
      "total_data_size": begin
        dma_config.total_transfer_size = item.a_data;
        `uvm_info(`gfn, $sformatf("Got total_data_size = %0d B",
                                  dma_config.total_transfer_size), UVM_HIGH)
      end
      "transfer_width": begin
        dma_config.per_transfer_width = dma_transfer_width_e'(
                                            `gmv(ral.transfer_width.transaction_width));
        `uvm_info(`gfn, $sformatf("Got transfer_width = %s",
                                  dma_config.per_transfer_width.name()), UVM_HIGH)
      end
      "control": begin
        // bit to indicate start of DMA operation
        bit go = `gmv(ral.control.go);
        `uvm_info(`gfn, $sformatf("Got GO = %0b", go), UVM_HIGH)
        // Get mirrored field value and cast to associated enum in dma_config
        dma_config.opcode = opcode_e'(`gmv(ral.control.opcode));
        `uvm_info(`gfn, $sformatf("Got opcode = %s", dma_config.opcode.name()), UVM_HIGH)
        if (go) begin
          // TODO Do checks once operation starts
        end
      end
      default: begin
        `uvm_info(`gfn, $sformatf("%s not processed", csr.get_name()), UVM_MEDIUM)
      end
    endcase
  endfunction

  // Method to process DMA register read
  function void process_reg_read(tl_seq_item item, uvm_reg csr);
    // After reads, if do_read_check is set, compare the mirrored_value against item.d_data
    bit do_read_check = 1'b1;
    `uvm_info(`gfn, $sformatf("Got reg_read to %s with addr : %0x and data : %0x ",
                              csr.get_name(), item.a_addr, item.a_data), UVM_HIGH)
    case (csr.get_name())
      "intr_state": begin
        `uvm_info(`gfn, $sformatf("intr_state = %0x", item.d_data), UVM_MEDIUM)
        do_read_check = 1;
      end
      default: do_read_check = 1'b0;
    endcase

    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf("reg name: %0s",
                                                                    csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  endfunction

  // Main method to process transactions on register configuration interface
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;

    bit write = item.is_write();

    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("\naccess unexpected addr 0x%0h", csr_addr))
    end

    // The access is to a valid CSR, now process it.
    // writes -> update local variable and fifo at A-channel access
    // reads  -> update predication at address phase and compare at D-channel access
    if (write && channel == AddrChannel) begin
      process_reg_write(item, csr);
    end  // addr_phase_write

    if (!write && channel == DataChannel) begin
      process_reg_read(item,csr);
    end  // data_phase_read
  endtask : process_tl_access

endclass
