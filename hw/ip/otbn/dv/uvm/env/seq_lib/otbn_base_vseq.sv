// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Base class for all OTBN test sequences
//

class otbn_base_vseq extends cip_base_vseq #(
    .CFG_T               (otbn_env_cfg),
    .RAL_T               (otbn_reg_block),
    .COV_T               (otbn_env_cov),
    .VIRTUAL_SEQUENCER_T (otbn_virtual_sequencer)
  );
  `uvm_object_utils(otbn_base_vseq)
  `uvm_object_new

  // Load the contents of an ELF file into the DUT's memories, either by a DPI backdoor (if backdoor
  // is true) or with TL transactions.
  protected task load_elf(string path, bit backdoor);
    if (backdoor) begin
      load_elf_backdoor(path);
    end else begin
      load_elf_over_bus(path);
    end
  endtask

  // Load the contents of an ELF file into the DUT's memories by a DPI backdoor
  protected function void load_elf_backdoor(string path);
    if (!OtbnMemUtilLoadElf(cfg.mem_util, path)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to load ELF at `%0s'", path))
    end
  endfunction

  // Load the contents of an ELF file into the DUT's memories by TL transactions
  protected task load_elf_over_bus(string path);
    otbn_loaded_word to_load[$];

    // First, tell OtbnMemUtil to stage the ELF. This reads the file and stashes away the segments
    // we need. If something goes wrong, it will print a message to stderr, so we can just fail.
    if (!OtbnMemUtilStageElf(cfg.mem_util, path)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to stage ELF at `%0s'", path))
    end

    // Next, we need to get the data to be loaded across the "DPI barrier" and into SystemVerilog.
    // We make a queue of the things that need loading (in address order) and then shuffle it, so
    // that we load the memory in an arbitrary order
    get_queue_entries(1'b0, to_load);
    get_queue_entries(1'b1, to_load);
    to_load.shuffle();

    // Send the writes, one by one
    foreach (to_load[i]) begin
      csr_utils_pkg::mem_wr(to_load[i].for_imem ? ral.imem : ral.dmem,
                            to_load[i].offset,
                            to_load[i].data);
    end
  endtask

  protected function automatic void
  get_queue_entries(bit for_imem, ref otbn_loaded_word entries[$]);
    // Get the size of this memory (to make sure the number of loaded words makes sense)
    int unsigned mem_size = for_imem ? OTBN_IMEM_SIZE : OTBN_DMEM_SIZE;

    // Iterate over the segments for this memory
    int seg_count = OtbnMemUtilGetSegCount(cfg.mem_util, for_imem);
    for (int seg_idx = 0; seg_idx < seg_count; seg_idx++) begin

      // What offset and size (in 32 bit words) is this segment?
      bit [31:0] seg_off, seg_size;
      if (!OtbnMemUtilGetSegInfo(cfg.mem_util, for_imem, seg_idx, seg_off, seg_size)) begin
        `uvm_fatal(`gfn, $sformatf("Failed to get segment info for segment %0d.", seg_idx))
      end

      // Add each word.
      for (bit [31:0] i = 0; i < seg_size; i++) begin
        bit [31:0] word_off, data;
        otbn_loaded_word entry;

        word_off = seg_off + i;

        if (!OtbnMemUtilGetSegData(cfg.mem_util, for_imem, word_off, data)) begin
          `uvm_fatal(`gfn, $sformatf("Failed to get segment data at word offset %0d.", word_off))
        end

        // Since we know that the segment data lies in IMEM or DMEM and that this fits in the
        // address space, we know that the top two bits of the word address are zero.
        `DV_CHECK_FATAL(word_off[31:30] == 2'b00)

        // OtbnMemUtil should have checked that this address was valid for the given memory, but it
        // can't hurt to check again.
        `DV_CHECK_FATAL({word_off, 2'b00} < {2'b00, mem_size})

        entry.for_imem = for_imem;
        entry.offset   = word_off[21:0];
        entry.data     = data;
        entries.push_back(entry);
      end
    end
  endfunction

  // Start OTBN and then wait until done
  protected task run_otbn();
    uvm_reg_data_t cmd_val;

    // Set the "start" bit in cmd_val and write it to the "cmd" register to start OTBN.
    `DV_CHECK_FATAL(ral.cmd.start.get_n_bits == 1);
    cmd_val = 1 << ral.cmd.start.get_lsb_pos();

    `uvm_info(`gfn, $sformatf("\n\t ----| Starting OTBN"), UVM_MEDIUM)
    csr_utils_pkg::csr_wr(ral.cmd, cmd_val);

    // Now wait until OTBN has finished
    `uvm_info(`gfn, $sformatf("\n\t ----| Waiting for OTBN to finish"), UVM_MEDIUM)
    csr_utils_pkg::csr_spinwait(.ptr(ral.status.busy), .exp_data(1'b0));

    `uvm_info(`gfn, $sformatf("\n\t ----| OTBN finished"), UVM_MEDIUM)
   endtask

endclass : otbn_base_vseq
