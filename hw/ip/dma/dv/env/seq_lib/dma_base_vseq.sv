// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base class providing common methods required for DMA testing
class dma_base_vseq extends cip_base_vseq #(
  .RAL_T              (dma_reg_block),
  .CFG_T              (dma_env_cfg),
  .COV_T              (dma_env_cov),
  .VIRTUAL_SEQUENCER_T(dma_virtual_sequencer)
);

  `uvm_object_utils(dma_base_vseq)

  // response sequences
  dma_pull_seq #(.AddrWidth(HOST_ADDR_WIDTH)) seq_host;
  dma_pull_seq #(.AddrWidth(CTN_ADDR_WIDTH))  seq_ctn;
  dma_pull_seq #(.AddrWidth(SYS_ADDR_WIDTH))  seq_sys;

  // DMA configuration item
  dma_seq_item dma_config;

  // Access to CONTROL register
  semaphore sem_control;

  // Remember whether we have a pending Abort request?
  // (we cannot rely upon the RAL layer to retain this information because the CONTROL.abort field
  //  is Write Only to software)
  bit abort_pending;

  function new (string name = "");
    super.new(name);
    dma_config = dma_seq_item::type_id::create("dma_config");
    // response sequences
    seq_ctn  = dma_pull_seq #(.AddrWidth(CTN_ADDR_WIDTH))::type_id::create("seq_ctn");
    seq_host = dma_pull_seq #(.AddrWidth(HOST_ADDR_WIDTH))::type_id::create("seq_host");
    seq_sys  = dma_pull_seq #(.AddrWidth(SYS_ADDR_WIDTH))::type_id::create("seq_sys");
    // Create memory models
    seq_host.fifo = dma_handshake_mode_fifo#(
                                .AddrWidth(HOST_ADDR_WIDTH))::type_id::create("fifo_host");
    seq_ctn.fifo = dma_handshake_mode_fifo#(
                                .AddrWidth(CTN_ADDR_WIDTH))::type_id::create("fifo_ctn");
    seq_sys.fifo = dma_handshake_mode_fifo#(
                                .AddrWidth(SYS_ADDR_WIDTH))::type_id::create("fifo_sys");
    seq_host.mem = mem_model#(.AddrWidth(HOST_ADDR_WIDTH),
                                .DataWidth(HOST_DATA_WIDTH))::type_id::create("mem_host");
    seq_ctn.mem = mem_model#(.AddrWidth(CTN_ADDR_WIDTH),
                                .DataWidth(CTN_DATA_WIDTH))::type_id::create("mem_ctn");
    seq_sys.mem = mem_model#(.AddrWidth(SYS_ADDR_WIDTH),
                               .DataWidth(SYS_DATA_WIDTH))::type_id::create("mem_sys");

    // System bus is currently unavailable and untestable withing this DV environment,
    // so activate additional constraints to prevent it causing test failures.
    void'($value$plusargs("dma_dv_waive_system_bus=%0b", dma_config.dma_dv_waive_system_bus));
    `uvm_info(`gfn,
              $sformatf("dma_dv_waive_system_bus = %d", dma_config.dma_dv_waive_system_bus),
              UVM_LOW)

    // Mutual exclusion of CONTROL register accesses.
    sem_control = new(1);
  endfunction : new

  function void init_model();
    // Assign mem_model instance handle to config object
    cfg.mem_ctn = seq_ctn.mem;
    cfg.mem_host = seq_host.mem;
    cfg.mem_sys = seq_sys.mem;
    // Assign dma_handshake_mode_fifo instance handle to config object
    cfg.fifo_ctn = seq_ctn.fifo;
    cfg.fifo_host = seq_host.fifo;
    cfg.fifo_sys = seq_sys.fifo;
    // Initialize memory
    cfg.mem_host.init();
    cfg.mem_ctn.init();
    cfg.mem_sys.init();
    cfg.fifo_host.init();
    cfg.fifo_ctn.init();
    cfg.fifo_sys.init();
  endfunction

  // Randomization of DMA configuration and transfer properties; to be overridden in those
  // derived classes where further constraints are required.
  virtual function void randomize_item(ref dma_seq_item dma_config);
    `DV_CHECK_RANDOMIZE_FATAL(dma_config)
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_HIGH)
  endfunction

  // Set up randomized source data for the transfer
  function void randomize_src_data(bit [31:0] total_data_size);
    bit [31:0] offset;
    cfg.src_data = new[total_data_size];
    for (offset = 32'b0; offset < total_data_size; offset++) begin
      cfg.src_data[offset] = $urandom_range(0, 255);
      `uvm_info(`gfn, $sformatf("%0x: %0x", offset, cfg.src_data[offset]), UVM_DEBUG)
    end
  endfunction

  // Function to populate source memory model with pre-randomized, known source data for the current
  // chunk of the transfer
  function void populate_src_mem(asid_encoding_e asid, bit [63:0] start_addr,
                                 ref bit [7:0] src_data[],
                                 input bit [31:0] offset, input bit [31:0] size);
    // TODO: we should perhaps not be assuming a 32-bit data bus here.
    bit [63:0] end_addr = (start_addr + size + 3) & ~3;
    bit [63:0] addr = {start_addr[63:2], 2'd0};
    `uvm_info(`gfn, $sformatf("Populating ASID 0x%x address range [0x%0x,0x%0x)",
                              asid, addr, end_addr), UVM_MEDIUM)

    // Alas we must ensure that the first bus word is fully-defined because TL-UL host adapater
    // fetches only complete bus words and there are assertion checks on the TL-UL bus.
    while (addr < end_addr) begin
      // Ideally we would use 'X' instead of a defined pattern.
      bit [7:0] data = 32'hBAAD_F00D >> {addr[1:0], 3'd0};
      if (addr >= start_addr && addr - start_addr < size) begin
        // Valid source data
        data = src_data[offset];
        offset++;
      end
      case (asid)
        OtInternalAddr: begin
          cfg.mem_host.write_byte(addr, data);
        end
        SocControlAddr: begin
          cfg.mem_ctn.write_byte(addr, data);
        end
        SocSystemAddr: begin
          cfg.mem_sys.write_byte(addr, data);
        end
        default: begin
          `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
        end
      endcase
      addr++;
    end
  endfunction

  // Function to populate FIFO with pre-randomized, known source data
  function void populate_src_fifo(asid_encoding_e asid, ref bit [7:0] src_data[],
                                  input bit [31:0] offset, input bit [31:0] size);
    case (asid)
      OtInternalAddr: begin
        cfg.fifo_host.populate_fifo(src_data, offset, size);
      end
      SocControlAddr: begin
        cfg.fifo_ctn.populate_fifo(src_data, offset, size);
      end
      SocSystemAddr: begin
        cfg.fifo_sys.populate_fifo(src_data, offset, size);
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
      end
    endcase
  endfunction

  function void supply_data(ref dma_seq_item dma_config, bit [31:0] offset, bit [31:0] size);
    `uvm_info(`gfn, $sformatf("Supplying bytes [0x%0x,0x%0x) of 0x%0x-byte transfer",
                    offset, offset + size, dma_config.total_data_size), UVM_MEDIUM)

    // Configure Source model
    if (dma_config.get_read_fifo_en()) begin
      // Supply a block of data for this transfer
      populate_src_fifo(dma_config.src_asid, cfg.src_data, offset, size);
    end else begin
      // The source address depends upon the configuration; chunks may overlap each other for
      // hardware-handshaking mode.
      bit [31:0] src_addr = dma_config.src_addr;
      if (!dma_config.handshake ||
          (dma_config.direction == DmaSendData && dma_config.auto_inc_buffer)) begin
        src_addr += offset;
      end else begin
        src_addr += offset % dma_config.chunk_data_size;
      end

      // Randomise mem_model data
      populate_src_mem(dma_config.src_asid, src_addr, cfg.src_data, offset, size);
    end
  endfunction

  // Function to set dma_handshake_mode_fifo mode settings
  function void set_model_fifo_mode(asid_encoding_e asid,
                                    bit [63:0] start_addr = '0,
                                    dma_transfer_width_e per_transfer_width,
                                    bit [31:0] max_size);
    start_addr[1:0] = 2'd0; // Address generated by DMA is 4B aligned
    case (asid)
      OtInternalAddr: begin
        cfg.fifo_host.enable_fifo(.fifo_base (start_addr), .per_transfer_width(per_transfer_width),
                                  .max_size (max_size));
      end
      SocControlAddr: begin
        cfg.fifo_ctn.enable_fifo(.fifo_base (start_addr), .per_transfer_width(per_transfer_width),
                                 .max_size (max_size));
      end
      SocSystemAddr: begin
        cfg.fifo_sys.enable_fifo(.fifo_base (start_addr), .per_transfer_width(per_transfer_width),
                                 .max_size (max_size));
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
      end
    endcase
  endfunction

  // Configure the source and destination models (memory models or FIFOs) appropriately for the
  // current chunk of the DMA transfer, starting at the given byte offset.
  // Returns the byte offset of the next chunk to be transferred, if any.
  function bit [31:0] configure_mem_model(ref dma_seq_item dma_config, input bit [31:0] offset);
    // Decide how many bytes of data to supply in this chunk
    bit [31:0] chunk_size = dma_config.total_data_size - offset;
    if (chunk_size > dma_config.chunk_data_size) begin
      chunk_size = dma_config.chunk_data_size;
    end

    // Empty source and destination memories of data from any previous chunks transferred.
    clear_memory();
    clear_fifo();

    // Configure Source model
    if (dma_config.get_read_fifo_en()) begin
      // Enable read FIFO mode in models
      set_model_fifo_mode(dma_config.src_asid, dma_config.src_addr, dma_config.per_transfer_width,
                          chunk_size);
    end else begin
      // The source address depends upon the configuration; chunks may overlap each other for
      // hardware-handshaking mode.
      bit [31:0] src_addr = dma_config.src_addr;
      if (!dma_config.handshake ||
          (dma_config.direction == DmaSendData && dma_config.auto_inc_buffer)) begin
        src_addr += offset;
      end
    end

    // Supply the next chunk of data for this transfer
    supply_data(dma_config, offset, chunk_size);

    // Configure Destination model
    if (dma_config.get_write_fifo_en()) begin
      // TODO: Presently there is no way to intervene and check per-chunk data, so gather it all
      // into a single large FIFO and the scoreboard will check it all at the end of the transfer.
      bit [31:0] max_size = chunk_size;
      if (dma_config.handshake && dma_config.direction == DmaSendData) begin
        max_size = dma_config.total_data_size;
      end

      // Enable write FIFO mode in models
      set_model_fifo_mode(dma_config.dst_asid, dma_config.dst_addr, dma_config.per_transfer_width,
                          max_size);
    end

    // Return the updated byte offset within the transfer
    return offset + chunk_size;
  endfunction

  // Set hardware handshake interrupt bits based on randomized class item
  function void set_hardware_handshake_intr(
    bit [dma_reg_pkg::NumIntClearSources-1:0] handshake_value);
    cfg.dma_vif.handshake_i = handshake_value;
  endfunction

  function void release_hardware_handshake_intr();
    cfg.dma_vif.handshake_i = '0;
  endfunction

  // Task: Write to Source Address CSR
  task set_source_address(bit [63:0] source_address);
    `uvm_info(`gfn, $sformatf("DMA: Source Address = 0x%016h", source_address), UVM_HIGH)
    csr_wr(ral.source_address_lo, source_address[31:0]);
    csr_wr(ral.source_address_hi, source_address[63:32]);
  endtask : set_source_address

  // Task: Write to Destination Address CSR
  task set_destination_address(bit [63:0] destination_address);
    csr_wr(ral.destination_address_lo, destination_address[31:0]);
    csr_wr(ral.destination_address_hi, destination_address[63:32]);
    `uvm_info(`gfn, $sformatf("DMA: Destination Address = 0x%016h", destination_address), UVM_HIGH)
  endtask : set_destination_address

  task set_destination_address_range(bit[63:0] almost_limit,
                                     bit[63:0] limit);
    csr_wr(ral.destination_address_limit_lo, limit[31:0]);
    csr_wr(ral.destination_address_limit_hi, limit[63:32]);
    `uvm_info(`gfn, $sformatf("DMA: Destination Limit = 0x%016h", limit), UVM_HIGH)
    csr_wr(ral.destination_address_almost_limit_lo, almost_limit[31:0]);
    csr_wr(ral.destination_address_almost_limit_hi, almost_limit[63:32]);
    `uvm_info(`gfn, $sformatf("DMA: Destination Almost Limit = 0x%016h", almost_limit), UVM_HIGH)
  endtask : set_destination_address_range

  // Task: Set DMA Enabled Memory base and limit
  task set_dma_enabled_memory_range(bit [32:0] base, bit [31:0] limit, bit valid, mubi4_t lock);
    csr_wr(ral.enabled_memory_range_base, base);
    `uvm_info(`gfn, $sformatf("DMA: DMA Enabled Memory base = %0x08h", base), UVM_HIGH)
    csr_wr(ral.enabled_memory_range_limit, limit);
    `uvm_info(`gfn, $sformatf("DMA: DMA Enabled Memory limit = %0x08h", limit), UVM_HIGH)
    csr_wr(ral.range_valid, valid);
    `uvm_info(`gfn, $sformatf("DMA: DMA Enabled Memory Range valid = %0d", valid), UVM_HIGH)
    if (lock != MuBi4True) begin
      csr_wr(ral.range_regwen, int'(lock));
      `uvm_info(`gfn, $sformatf("DMA: DMA Enabled Memory lock = %s", lock.name()), UVM_HIGH)
    end
  endtask : set_dma_enabled_memory_range

  // Task: Write to Source and Destination Address Space ID (ASID)
  task set_address_space_id(asid_encoding_e src_asid, asid_encoding_e dst_asid);
    ral.address_space_id.source_asid.set(int'(src_asid));
    ral.address_space_id.destination_asid.set(int'(dst_asid));
    csr_update(.csr(ral.address_space_id));
    `uvm_info(`gfn, $sformatf("DMA: Source ASID = %d", src_asid), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("DMA: Destination ASID = %d", dst_asid), UVM_HIGH)
  endtask : set_address_space_id

  // Task: Set number of bytes to transfer
  task set_total_size(bit [31:0] total_data_size);
    csr_wr(ral.total_data_size, total_data_size);
    `uvm_info(`gfn, $sformatf("DMA: Total Data Size = %d", total_data_size), UVM_HIGH)
  endtask : set_total_size

  // Task: Set number of bytes per chunk to transfer
  task set_chunk_data_size(bit [31:0] chunk_data_size);
    csr_wr(ral.chunk_data_size, chunk_data_size);
    `uvm_info(`gfn, $sformatf("DMA: Chunk Data Size = %d", chunk_data_size), UVM_HIGH)
  endtask : set_chunk_data_size

  // Task: Set Byte size of each transfer (0:1B, 1:2B, 2:3B, 3:4B)
  task set_transfer_width(dma_transfer_width_e transfer_width);
    csr_wr(ral.transfer_width, transfer_width);
    `uvm_info(`gfn, $sformatf("DMA: Transfer Byte Size = %d",
                              transfer_width.name()), UVM_HIGH)
  endtask : set_transfer_width

  // Task: Set handshake interrupt register
  task set_handshake_int_regs(ref dma_seq_item dma_config);
    `uvm_info(`gfn, "Set DMA Handshake mode interrupt registers", UVM_HIGH)
    csr_wr(ral.clear_int_src, dma_config.clear_int_src);
    csr_wr(ral.clear_int_bus, dma_config.clear_int_bus);
    foreach (dma_config.int_src_addr[i]) begin
      csr_wr(ral.int_source_addr[i], dma_config.int_src_addr[i]);
      csr_wr(ral.int_source_wr_val[i], dma_config.int_src_wr_val[i]);
    end
    ral.handshake_interrupt_enable.set(dma_config.handshake_intr_en);
    csr_update(ral.handshake_interrupt_enable);
  endtask : set_handshake_int_regs

  // Task: Configure DMA controller to perform a transfer
  // (common to both 'memory-to-memory' and 'hardware handshaking' modes of operation)
  task run_common_config(ref dma_seq_item dma_config);
    `uvm_info(`gfn, "DMA: Start Common Configuration", UVM_HIGH)
    // Not yet requested an Abort during this transaction.
    abort_pending = 1'b0;
    set_source_address(dma_config.src_addr);
    set_destination_address(dma_config.dst_addr);
    set_destination_address_range(dma_config.mem_buffer_almost_limit,
                                  dma_config.mem_buffer_limit);
    set_address_space_id(dma_config.src_asid, dma_config.dst_asid);
    set_total_size(dma_config.total_data_size);
    set_chunk_data_size(dma_config.chunk_data_size);
    set_transfer_width(dma_config.per_transfer_width);
    randomize_src_data(dma_config.total_data_size);
    void'(configure_mem_model(dma_config, 32'd0));
    set_handshake_int_regs(dma_config);
    set_dma_enabled_memory_range(dma_config.mem_range_base,
                                 dma_config.mem_range_limit,
                                 dma_config.mem_range_valid,
                                 dma_config.mem_range_lock);
  endtask : run_common_config

  // Task: Enable/Disable Interrupt(s)
  task enable_interrupts(bit [31:0] interrupts = 32'hFFFF_FFFF, bit enable = 1'b1);
    string action;
    action = enable ? "Enable" : "Disable";
    `uvm_info(`gfn, $sformatf("DMA: %s interrupt(s) 0x%0x", action, interrupts), UVM_HIGH)
    cfg_interrupts(interrupts, enable);
  endtask : enable_interrupts

  // Clear one or more interrupts
  task clear_interrupts(bit [31:0] clear);
    `uvm_info(`gfn, $sformatf("DMA: Clear Interrupt(s) 0x%0x", clear), UVM_HIGH)
    csr_wr(ral.intr_state, clear);
  endtask : clear_interrupts

  // Task: Enable Handshake Interrupt Enable
  task enable_handshake_interrupt();
    `uvm_info(`gfn, "DMA: Assert Interrupt Enable", UVM_HIGH)
    csr_wr(ral.handshake_interrupt_enable, 32'd1);
  endtask : enable_handshake_interrupt

  // Enable/disable errors on TL-UL buses with the given percentage probability/word
  function void enable_bus_errors(int pct);
    seq_ctn.enable_bus_errors(pct);
    seq_sys.enable_bus_errors(pct);
    seq_host.enable_bus_errors(pct);
  endfunction

  function void set_seq_fifo_read_mode(asid_encoding_e asid, bit read_fifo_en);
    case (asid)
      OtInternalAddr: begin
        seq_host.read_fifo_en = read_fifo_en;
        `uvm_info(`gfn, $sformatf("set host read_fifo_en = %0b", read_fifo_en), UVM_HIGH)
      end
      SocControlAddr: begin
        seq_ctn.read_fifo_en = read_fifo_en;
        `uvm_info(`gfn, $sformatf("set ctn read_fifo_en = %0b", read_fifo_en), UVM_HIGH)
      end
      SocSystemAddr: begin
        seq_sys.read_fifo_en = read_fifo_en;
        `uvm_info(`gfn, $sformatf("set sys read_fifo_en = %0b", read_fifo_en), UVM_HIGH)
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
      end
    endcase
  endfunction

  function void set_seq_fifo_write_mode(asid_encoding_e asid, bit write_fifo_en);
    case (asid)
      OtInternalAddr: begin
        seq_host.write_fifo_en = write_fifo_en;
        `uvm_info(`gfn, $sformatf("set host write_fifo_en = %0b", write_fifo_en), UVM_HIGH)
      end
      SocControlAddr: begin
        seq_ctn.write_fifo_en = write_fifo_en;
        `uvm_info(`gfn, $sformatf("set ctn write_fifo_en = %0b", write_fifo_en), UVM_HIGH)
      end
      SocSystemAddr: begin
        seq_sys.write_fifo_en = write_fifo_en;
        `uvm_info(`gfn, $sformatf("set sys write_fifo_en = %0b", write_fifo_en), UVM_HIGH)
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
      end
    endcase
  endfunction

  // Task: Start TLUL Sequences
  virtual task start_device(ref dma_seq_item dma_config);
    if (dma_config.handshake) begin
      // Will the test sequence generate any interrupts?
      bit [31:0] fifo_interrupt_mask;
      fifo_interrupt_mask = dma_config.handshake_intr_en &  // Any handshaking interrupts enabled
                            dma_config.lsio_trigger_i;      // .. and being driven by test seq?
      `DV_CHECK_EQ(|fifo_interrupt_mask, 1'b1, "Handshake test has no enabled interrupt sources")

      `uvm_info(`gfn, $sformatf("FIFO interrupt enable mask = %0x ", fifo_interrupt_mask),
                UVM_HIGH)
      // Set fifo enable bit
      set_seq_fifo_read_mode(dma_config.src_asid, dma_config.get_read_fifo_en());
      set_seq_fifo_write_mode(dma_config.dst_asid, dma_config.get_write_fifo_en());

      // TODO: there may be some merit at some point to starting handshaking transfers when
      // interrupts cannot occur, but only if we're expecting to abort transfers, for example.
      if (|fifo_interrupt_mask) begin
        bit host_en = 1'b0;
        bit ctn_en = 1'b0;
        // Get FIFO interrupt register address and value
        // Find the interrupt index with both handshake interrupt enable and clear_int_src
        for (int i = 0; i < dma_reg_pkg::NumIntClearSources; i++) begin
          // Instruct memory/FIFO models on the appropriate bus(es) to expect 'Clear Interrupt'
          // writes, so that they may be excluded from normal traffic.
          if (dma_config.clear_int_src[i]) begin
            `uvm_info(`gfn, $sformatf("Clear Interrupt writes expected for source %d on bus %d", i,
                                      dma_config.clear_int_bus[i]), UVM_HIGH)
            // Set FIFO interrupt clear address and values in corresponding pull sequence instance
            case (dma_config.clear_int_bus[i])
              0: begin
                seq_ctn.add_fifo_reg(dma_config.int_src_addr[i], dma_config.int_src_wr_val[i]);
                ctn_en = 1'b1;
              end
              default: begin
                seq_host.add_fifo_reg(dma_config.int_src_addr[i], dma_config.int_src_wr_val[i]);
                host_en = 1'b1;
              end
            endcase
          end
        end
        // Set FIFO interrupt clear in corresponding pull sequence instance(s)
        if (ctn_en)  seq_ctn.set_fifo_clear(1'b1);
        if (host_en) seq_host.set_fifo_clear(1'b1);
      end
    end

    // Each of the sequences must be told the bytes/transaction in order to count the bytes read
    seq_host.set_txn_bytes(dma_config.txn_bytes());
    seq_ctn.set_txn_bytes(dma_config.txn_bytes());
    seq_sys.set_txn_bytes(dma_config.txn_bytes());

    `uvm_info(`gfn, "DMA: Starting Devices", UVM_HIGH)
    fork
      seq_ctn.start(p_sequencer.tl_sequencer_dma_ctn_h);
      seq_host.start(p_sequencer.tl_sequencer_dma_host_h);
      seq_sys.start(p_sequencer.tl_sequencer_dma_sys_h);
    join_none
  endtask : start_device

  // Method to terminate sequences gracefully
  virtual task stop_device();
    `uvm_info(`gfn, "DMA: Stopping Devices", UVM_HIGH)
    fork
      seq_ctn.seq_stop();
      seq_host.seq_stop();
      seq_sys.seq_stop();
    join
    // Clear FIFO mode enable bit
    set_seq_fifo_read_mode(OtInternalAddr, 0);
    set_seq_fifo_read_mode(SocControlAddr, 0);
    set_seq_fifo_read_mode(SocSystemAddr, 0);
    set_seq_fifo_write_mode(OtInternalAddr, 0);
    set_seq_fifo_write_mode(SocControlAddr, 0);
    set_seq_fifo_write_mode(SocSystemAddr, 0);
    // Clear FIFO write clear enable bit
    seq_ctn.set_fifo_clear(0);
    seq_host.set_fifo_clear(0);
    seq_sys.set_fifo_clear(0);
    // Disable FIFO
    cfg.fifo_host.disable_fifo();
    cfg.fifo_ctn.disable_fifo();
    cfg.fifo_sys.disable_fifo();
  endtask

  // Method to clear memory models of any content
  function void clear_memory();
    // Clear memory contents
    `uvm_info(`gfn, $sformatf("Clearing memory contents"), UVM_MEDIUM)
    cfg.mem_host.init();
    cfg.mem_ctn.init();
    cfg.mem_sys.init();
  endfunction

  // Method to clear FIFO models of any content
  function void clear_fifo();
    // Clear FIFO contents
    `uvm_info(`gfn, $sformatf("Clearing FIFO contents"), UVM_MEDIUM)
    cfg.fifo_host.init();
    cfg.fifo_ctn.init();
    cfg.fifo_sys.init();
  endfunction

  // Task: Set the CONTROL register, optionally commencing a transfer.
  task set_control(opcode_e opcode,
                   bit initial_transfer,
                   bit handshake,
                   bit auto_inc_buffer,
                   bit auto_inc_fifo,
                   bit data_direction,
                   bit go);   // Commence transfer?
    uvm_reg_data_t data = 0;
    string action;

    action = go ? "Executing" : "Setting";
    `uvm_info(`gfn, $sformatf(
              "DMA: %s CONTROL OpC=%d Initial=%d Handshake=%d inc_buffer=%d inc_fifo=%d dir=%d",
                action, opcode, initial_transfer, handshake, auto_inc_buffer, auto_inc_fifo,
                data_direction),
              UVM_HIGH)

    // Exclusive access to CONTROL register
    // Note: a parallel thread may be attempting to Abort transfers using the CONTROL register.
    sem_control.get(1);

    // Configure all fields except GO bit which shall initially be clear
    // Note: Importantly we must perform this whilst we have exclusive access and we must preserve
    // the state of the 'abort' bit, so that we do not remove a requested Abort.

    data = get_csr_val_with_updated_field(ral.control.opcode, data, int'(opcode));
    data = get_csr_val_with_updated_field(ral.control.initial_transfer, data, initial_transfer);
    data = get_csr_val_with_updated_field(ral.control.hardware_handshake_enable, data, handshake);
    data = get_csr_val_with_updated_field(ral.control.memory_buffer_auto_increment_enable, data,
                                          auto_inc_buffer);
    data = get_csr_val_with_updated_field(ral.control.fifo_auto_increment_enable, data,
                                          auto_inc_fifo);
    data = get_csr_val_with_updated_field(ral.control.data_direction, data, data_direction);
    data = get_csr_val_with_updated_field(ral.control.abort, data, abort_pending);
    data = get_csr_val_with_updated_field(ral.control.go, data, 1'b0);

    csr_wr(ral.control, data);
    // Set GO bit to start operation (chunk/transfer)?
    if (go) begin
      data = get_csr_val_with_updated_field(ral.control.go, data, 1'b1);
      csr_wr(ral.control, data);
    end

    sem_control.put(1);
  endtask : set_control

  // Start the transfer of a chunk of data.
  task start_chunk(ref dma_seq_item dma_config,
                   input bit initial_transfer);  // Is this the first chunk of the transfer?
    set_control(dma_config.opcode,
                initial_transfer,
                dma_config.handshake,
                dma_config.auto_inc_buffer,
                dma_config.auto_inc_fifo,
                dma_config.direction,
                1'b1); // Go
  endtask

  // Clear 'STATUS.abort' field after an Abort request has been actioned.
  task clear_aborted();
    `uvm_info(`gfn, "DMA: Clear STATUS.abort", UVM_HIGH)
    ral.status.aborted.set(1'b1);
    csr_update(.csr(ral.status));
  endtask : clear_aborted

  // Clear 'STATUS.done' field after a transfer has completed.
  task clear_done();
    `uvm_info(`gfn, "DMA: Clear STATUS.done", UVM_HIGH)
    ral.status.done.set(1'b1);
    csr_update(.csr(ral.status));
  endtask : clear_done

  // Task: Abort the current transaction
  task abort();
    uvm_reg_data_t data = 0;

    `uvm_info(`gfn, "Aborting transfer", UVM_MEDIUM)

    // Exclusive access to CONTROL register
    // Note: may be called by a thread that is parallel to the main vseq.
    sem_control.get(1);
    // Remember that we have requested an abort, so that we do not clear it in `set_control.`
    abort_pending = 1'b1;

    data = get_csr_val_with_updated_field(ral.control.abort, data, 1'b1);
    csr_wr(ral.control, data);

    sem_control.put(1);
  endtask : abort

  // Task: Wait for Completion
  task wait_for_completion(bit intr_driven, output status_t status);
    int timeout = 1000000;
    status = 0;
    fork
      // Timeout condition due to simulation hang
      begin
        delay(timeout);
        `uvm_fatal(`gfn, $sformatf("ERROR: Timeout Condition Reached at %d cycles", timeout))
      end
      // Completion detection when interrupt driven
      await_interrupt(intr_driven, status);
      // Completion signaling when we're just polling CSRs
      // Note: this thread is the only one that completes, which is important because terminating
      // the CSR polling may leave the RAL locked.
      poll_status(intr_driven, status);
    join_any
    disable fork;

    // Presently, since the scoreboard is substantially updated by reads of the STATUS register,
    // we need to ensure that at least one such read occurs.
    if (intr_driven) begin
      poll_status(1'b0, status, 0);
    end
  endtask : wait_for_completion

  // Await the receipt of an interrupt from the DMA controller.
  task await_interrupt(bit intr_driven, ref status_t status);
    if (intr_driven) begin
      forever begin
        delay(1);
        if (cfg.intr_vif.pins[DMA_DONE])  status[StatusDone]  = 1'b1;
        if (cfg.intr_vif.pins[DMA_ERROR]) status[StatusError] = 1'b1;
      end
    end else begin
      // Rely upon the CSR reading in `poll_status` to detect completion.
      forever delay(100);
    end
  endtask : await_interrupt

  // Task: Continuously poll status until completion every N cycles
  task poll_status(bit intr_driven, ref status_t status, input int pollrate = 10);
    bit [31:0] v;

    `uvm_info(`gfn, "DMA: Polling DMA Status", UVM_HIGH)
    do begin
      csr_rd(ral.status, v);
      // Collect some STATUS bit that do not generate interrupts, and inform parallel threads
      // if (v[0]) ->e_busy;
      if (v[2]) status[StatusAborted] = 1'b1;
      // Respond to the STATUS.done and STATUS.error bits only if we're not insisting upon
      // interrupt-driven completion.
      if (!intr_driven) begin
        if (v[1]) status[StatusDone]  = 1'b1;
        if (v[3]) status[StatusError] = 1'b1;
      end
      // Note: sha2_digest_valid is not a completion event
      // v[12]
      delay(pollrate);
    end while (~|status);
  endtask : poll_status

  // Task: Simulate a clock delay
  virtual task delay(int num = 1);
    cfg.clk_rst_vif.wait_clks(num);
  endtask : delay

  // Task to wait for the transfer of a specified number of bytes.
  //
  // The `stop` signal may be set by a parallel task that monitors the completion of chunks,
  // to ensure the tidy exit of this task. (In a multi-chunk transfer the generation of
  // LSIO triggers is decoupled from the transfers.)
  task wait_num_bytes_transfer(uint num_bytes, ref bit stop);
    while (!stop) begin
      if (get_bytes_written(dma_config) >= num_bytes) begin
        `uvm_info(`gfn, $sformatf("Got %d", num_bytes), UVM_DEBUG)
        break;
      end else begin
        delay(1);
      end
    end
  endtask

  // Task to read out the SHA digest
  task read_sha2_digest(input opcode_e op, output logic [511:0] digest);
    int sha_digest_size; // in 32-bit words
    string sha_mode;
    digest = '0;
    `uvm_info(`gfn, "DMA: Read SHA2 digest", UVM_MEDIUM)
    case (op)
      OpcSha256: begin
        sha_digest_size = 8;
        sha_mode = "SHA2-256";
      end
      OpcSha384: begin
        sha_digest_size = 12;
        sha_mode = "SHA2-384";
      end
      OpcSha512: begin
        sha_digest_size = 16;
        sha_mode = "SHA2-512";
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported SHA2 opcode %d", op))
      end
    endcase

    for(int i = 0; i < sha_digest_size; ++i) begin
      csr_rd(ral.sha2_digest[i],  digest[i*32 +: 32]);
    end
    `uvm_info(`gfn, $sformatf("DMA: %s digest: %x", sha_mode, digest), UVM_MEDIUM)
  endtask

  // Return number of bytes read from interface corresponding to source ASID
  virtual function uint get_bytes_read(ref dma_seq_item dma_config);
    case (dma_config.src_asid)
      OtInternalAddr: begin
        `uvm_info(`gfn,
                  $sformatf("OTInternal bytes_read = %0d", seq_host.bytes_read), UVM_HIGH)
        return seq_host.bytes_read;
      end
      SocControlAddr: begin
        `uvm_info(`gfn,
                  $sformatf("SocControlAddr bytes_read = %0d", seq_ctn.bytes_read), UVM_HIGH)
        return seq_ctn.bytes_read;
      end
      SocSystemAddr: begin
        `uvm_info(`gfn,
                  $sformatf("SocSystemAddr bytes_read = %0d", seq_sys.bytes_read), UVM_HIGH)
        return seq_sys.bytes_read;
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", dma_config.src_asid))
      end
    endcase
  endfunction

  // Return number of bytes written to interface corresponding to destination ASID
  virtual function uint get_bytes_written(ref dma_seq_item dma_config);
    case (dma_config.dst_asid)
      OtInternalAddr: begin
        `uvm_info(`gfn,
                  $sformatf("OTInternal bytes_written = %0d", seq_host.bytes_written), UVM_HIGH)
        return seq_host.bytes_written;
      end
      SocControlAddr: begin
        `uvm_info(`gfn,
                  $sformatf("SocControlAddr bytes_written = %0d", seq_ctn.bytes_written), UVM_HIGH)
        return seq_ctn.bytes_written;
      end
      SocSystemAddr: begin
        `uvm_info(`gfn,
                  $sformatf("SocSystemAddr bytes_written = %0d", seq_sys.bytes_written), UVM_HIGH)
        return seq_sys.bytes_written;
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", dma_config.dst_asid))
      end
    endcase
  endfunction

  // Body: Need to override for inherited tests
  task body();
    init_model();
    enable_interrupts();
  endtask : body
endclass
