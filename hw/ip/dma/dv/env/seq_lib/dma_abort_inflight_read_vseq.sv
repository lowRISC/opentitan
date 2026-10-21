// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Abort a 'memory-to-memory' transfer whilst its first read or its first write is still awaiting a
// response, and then restart the transfer at once with new source data. The late response to the
// aborted request must not be taken as a response for the restarted transfer. Some iterations
// first restart with a new configuration and abort that too.
class dma_abort_inflight_read_vseq extends dma_base_vseq;
  `uvm_object_utils(dma_abort_inflight_read_vseq)
  `uvm_object_new

  // Number of transfers to abort and restart.
  rand uint num_txns;
  constraint num_txns_c {num_txns inside {[4:8]};}

  // Response delay (in clock cycles) of the aborted request; long enough for the transfer to be
  // aborted and restarted before the response arrives.
  rand uint abort_rsp_delay;
  constraint abort_rsp_delay_c {abort_rsp_delay inside {[200:500]};}

  // Whether the current iteration holds back the first write instead of the first read.
  bit hold_write;

  // Valid single-chunk copy operations with 4B transactions, reading from a TL-UL port. To hold
  // back only the first write, the destination uses the other TL-UL port.
  virtual function void randomize_item(ref dma_seq_item dma_config);
    dma_config.valid_dma_config = 1;
    dma_config.multi_chunk_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      dma_config,
      // TODO(#31929): Also read from the SoC System port once its requests are tracked.
      src_asid inside {OtInternalAddr, SocControlAddr};
      local::hold_write -> dst_asid inside {OtInternalAddr, SocControlAddr} &&
                           dst_asid != src_asid;
      chunk_data_size == total_data_size;
      per_transfer_width == DmaXfer4BperTxn;
      src_addr_inc && dst_addr_inc;
      handshake == 1'b0;
      opcode == OpcCopy;
      range_regwen == MuBi4True;)
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_HIGH)
  endfunction

  // Set the response delays of the TL-UL agent of the given address space only.
  function void set_agent_response_delays(asid_encoding_e asid, int min, int max);
    tl_agent_cfg agent_cfg = (asid == OtInternalAddr) ? cfg.tl_agent_dma_host_cfg
                                                      : cfg.tl_agent_dma_ctn_cfg;
    agent_cfg.use_seq_item_d_valid_delay = 1'b0;
    agent_cfg.d_valid_delay_min = min;
    agent_cfg.d_valid_delay_max = max;
  endfunction

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting abort in-flight read Sequence", UVM_LOW)
    super.body();

    for (uint i = 0; i < num_txns; i++) begin
      uint num_dropped = cfg.scoreboard_h.num_aborted_rsps_dropped;
      uint hold_delay;
      status_t status;
      // Whether to restart with a new configuration and abort that too, before the final restart.
      bit double_abort;
      `DV_CHECK_STD_RANDOMIZE_FATAL(double_abort)
      `DV_CHECK_STD_RANDOMIZE_FATAL(hold_write)

      randomize_item(dma_config);
      `DV_CHECK(dma_config.is_valid_config)
      run_common_config(dma_config);
      start_device(dma_config);

      // Hold back the response to the first read or write, and abort once it has been accepted.
      // Reconfiguring for a double abort takes longer, so hold the response back for longer too.
      hold_delay = abort_rsp_delay + (double_abort ? 1000 : 0);
      `uvm_info(`gfn, $sformatf("Holding back the first %s, double_abort = %0b",
                                string'(hold_write ? "write" : "read"), double_abort),
                UVM_MEDIUM)
      if (hold_write) begin
        set_response_delays(0, 10);
        set_agent_response_delays(dma_config.dst_asid, hold_delay, hold_delay);
      end else begin
        set_response_delays(hold_delay, hold_delay);
      end
      start_chunk(dma_config, 1'b1);
      if (hold_write) begin
        `DV_SPINWAIT(while (get_bytes_written(dma_config) == 0) delay(1);)
      end else begin
        `DV_SPINWAIT(while (get_bytes_read(dma_config) == 0) delay(1);)
      end
      abort();
      poll_status(1'b0, status);
      `DV_CHECK_EQ(status, 1 << StatusAborted)
      clear_aborted();

      // Restore the default response delays of the TL-UL agents for the restarted transfer.
      set_response_delays(0, 10);
      if (double_abort) begin
        // Restart with a new configuration and abort that at once.
        randomize_item(dma_config);
        `DV_CHECK(dma_config.is_valid_config)
        run_common_config(dma_config);
        start_chunk(dma_config, 1'b1);
        abort();
        // poll_status only sets bits, so clear those of the first abort.
        status = '0;
        poll_status(1'b0, status);
        `DV_CHECK_EQ(status, 1 << StatusAborted)
        clear_aborted();
      end

      // Restart at once with new source data. The aborted request may still await its response.
      randomize_src_data(dma_config.total_data_size);
      void'(configure_mem_model(dma_config, 32'd0));
      abort_pending = 1'b0;
      start_chunk(dma_config, 1'b1);
      // `wait_for_completion` ends with `disable fork`, which would kill the device sequences
      // started by `start_device`.
      fork
        wait_for_completion(1'b0, status);
      join
      `DV_CHECK_EQ(status, 1 << StatusDone)
      // The response to the aborted request must have arrived after a restart in this iteration.
      `DV_CHECK_EQ(cfg.scoreboard_h.num_aborted_rsps_dropped, num_dropped + 1)
      clear_done();

      stop_device();
    end
    `uvm_info(`gfn, "DMA: Completed abort in-flight read Sequence", UVM_LOW)
  endtask : body
endclass
