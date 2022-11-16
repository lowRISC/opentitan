// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "spike_cosim_dpi.svh"
`include "cosim_dpi.svh"

class ibex_cosim_scoreboard extends uvm_scoreboard;
  import ibex_pkg::*;
  chandle cosim_handle;

  core_ibex_cosim_cfg cfg;

  uvm_tlm_analysis_fifo #(ibex_rvfi_seq_item)       rvfi_port;
  uvm_tlm_analysis_fifo #(ibex_mem_intf_seq_item)   dmem_port;
  uvm_tlm_analysis_fifo #(ibex_mem_intf_seq_item)   imem_port;
  uvm_tlm_analysis_fifo #(ibex_ifetch_seq_item)     ifetch_port;
  uvm_tlm_analysis_fifo #(ibex_ifetch_pmp_seq_item) ifetch_pmp_port;

  virtual core_ibex_instr_monitor_if instr_vif;
  virtual core_ibex_dut_probe_if     dut_vif;

  uvm_event reset_e;
  uvm_event check_inserted_iside_error_e;

  bit failed_iside_accesses [bit[31:0]];
  bit iside_pmp_failure     [bit[31:0]];

  typedef struct {
    bit [63:0] order;
    bit [31:0] addr;
  } iside_err_t;

  iside_err_t iside_error_queue [$];

  `uvm_component_utils(ibex_cosim_scoreboard)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);

    rvfi_port                    = new("rvfi_port", this);
    dmem_port                    = new("dmem_port", this);
    imem_port                    = new("imem_port", this);
    ifetch_port                  = new("ifetch_port", this);
    ifetch_pmp_port              = new("ifetch_pmp_port", this);
    cosim_handle                 = null;
    reset_e                      = new();
    check_inserted_iside_error_e = new();
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(core_ibex_cosim_cfg)::get(this, "", "cosim_cfg", cfg)) begin
      `uvm_fatal(`gfn, "Cannot get cosim configuration")
    end

    if (!uvm_config_db#(virtual core_ibex_instr_monitor_if)::get(null, "", "instr_monitor_if",
                                                                 instr_vif)) begin
      `uvm_fatal(`gfn, "Cannot get instr_monitor_if")
    end

    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if",
                                                                 dut_vif)) begin
      `uvm_fatal(`gfn, "Cannot get dut_probe_if")
    end

    init_cosim();
  endfunction : build_phase

  protected function void init_cosim();
    cleanup_cosim();

    // TODO: Ensure log file on reset gets append rather than overwrite?
    cosim_handle = spike_cosim_init(cfg.isa_string, cfg.start_pc, cfg.start_mtvec, cfg.log_file,
      cfg.pmp_num_regions, cfg.pmp_granularity, cfg.mhpm_counter_num, cfg.secure_ibex, cfg.icache);

    if (cosim_handle == null) begin
      `uvm_fatal(`gfn, "Could not initialise cosim")
    end
  endfunction

  protected function void cleanup_cosim();
     if (cosim_handle) begin
        spike_cosim_release(cosim_handle);
     end
     cosim_handle = null;
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      @(negedge instr_vif.reset)
      fork : isolation_fork
        run_cosim_rvfi();
        run_cosim_dmem();
        run_cosim_imem_errors();
        run_cosim_prune_imem_errors();
        if (cfg.probe_imem_for_errs) begin
          run_cosim_imem();
        end else begin
          fork
            run_cosim_ifetch();
            run_cosim_ifetch_pmp();
          join_any
        end
      join_none
      reset_e.wait_trigger();
      disable fork;
      handle_reset();
    end // forever
  endtask : run_phase

  task run_cosim_rvfi();
    ibex_rvfi_seq_item rvfi_instr;

    forever begin
      rvfi_port.get(rvfi_instr);

      if (iside_error_queue.size() > 0) begin
        // Remove entries from iside_error_queue where the instruction never reaches the RVFI
        // interface because it was flushed.
        while (iside_error_queue.size() > 0 && iside_error_queue[0].order < rvfi_instr.order) begin
          iside_error_queue.pop_front();
        end

        // Check if the top of the iside_error_queue relates to the current RVFI instruction. If so
        // notify the cosim environment of an instruction error.
        if (iside_error_queue.size() !=0 && iside_error_queue[0].order == rvfi_instr.order) begin
          riscv_cosim_set_iside_error(cosim_handle, iside_error_queue[0].addr);
          iside_error_queue.pop_front();
        end
      end

      riscv_cosim_set_nmi(cosim_handle, rvfi_instr.nmi);
      riscv_cosim_set_nmi_int(cosim_handle, rvfi_instr.nmi_int);
      riscv_cosim_set_mip(cosim_handle, rvfi_instr.mip);
      riscv_cosim_set_debug_req(cosim_handle, rvfi_instr.debug_req);
      riscv_cosim_set_mcycle(cosim_handle, rvfi_instr.mcycle);

      // Set performance counters through a pseudo-backdoor write
      for (int i=0; i < 10; i++) begin
        riscv_cosim_set_csr(cosim_handle, CSR_MHPMCOUNTER3 + i, rvfi_instr.mhpmcounters[i]);
        riscv_cosim_set_csr(cosim_handle, CSR_MHPMCOUNTER3H + i, rvfi_instr.mhpmcountersh[i]);
      end

      riscv_cosim_set_ic_scr_key_valid(cosim_handle, rvfi_instr.ic_scr_key_valid);

      if (!riscv_cosim_step(cosim_handle, rvfi_instr.rd_addr, rvfi_instr.rd_wdata, rvfi_instr.pc,
                            rvfi_instr.trap, rvfi_instr.rf_wr_suppress)) begin
        // cosim instruction step doesn't match rvfi captured instruction, report a fatal error
        // with the details
        if (cfg.relax_cosim_check) begin
          `uvm_info(`gfn, get_cosim_error_str(), UVM_LOW)
        end else begin
          `uvm_fatal(`gfn, get_cosim_error_str())
        end
      end
    end
  endtask: run_cosim_rvfi

  task run_cosim_dmem();
    ibex_mem_intf_seq_item mem_op;

    forever begin
      dmem_port.get(mem_op);
      // Notify the cosim of all dside accesses emitted by the RTL
      riscv_cosim_notify_dside_access(cosim_handle, mem_op.read_write == WRITE, mem_op.addr,
        mem_op.data, mem_op.be, mem_op.error, mem_op.misaligned_first, mem_op.misaligned_second);
    end
  endtask: run_cosim_dmem

  task run_cosim_imem();
    ibex_mem_intf_seq_item mem_op;

    forever begin
      // Take stream of transaction from imem monitor. Where an imem access has an error record it
      // in failed_iside_accesses. If an access has succeeded remove it from failed_imem_accesses if
      // it's there.
      // Note all transactions are 32-bit aligned.
      imem_port.get(mem_op);
      if (mem_op.error) begin
        failed_iside_accesses[mem_op.addr] = 1'b1;
      end else begin
        if (failed_iside_accesses.exists(mem_op.addr)) begin
          failed_iside_accesses.delete(mem_op.addr);
        end
      end
    end
  endtask: run_cosim_imem

  task run_cosim_ifetch();
    ibex_ifetch_seq_item ifetch;
    bit [31:0] aligned_fetch_addr;
    bit [31:0] aligned_fetch_addr_next;

    forever begin
      ifetch_port.get(ifetch);
      aligned_fetch_addr = {ifetch.fetch_addr[31:2], 2'b0};
      aligned_fetch_addr_next = aligned_fetch_addr + 32'd4;

      if (ifetch.fetch_err) begin
        // Instruction error observed in fetch stage
        bit [31:0] failing_addr;

        // Determine which address failed.
        if (ifetch.fetch_err_plus2) begin
          // Instruction crosses a 32-bit boundary and second half failed
          failing_addr = aligned_fetch_addr_next;
        end else begin
          failing_addr = aligned_fetch_addr;
        end

        failed_iside_accesses[failing_addr] = 1'b1;
      end else begin
        if (ifetch.fetch_addr[1:0] != 0 && ifetch.fetch_rdata[1:0] == 2'b11) begin
          // Instruction crosses 32-bit boundary, so remove any failed accesses on the other side of
          // the 32-bit boundary.
          if (failed_iside_accesses.exists(aligned_fetch_addr_next)) begin
            failed_iside_accesses.delete(aligned_fetch_addr_next);
          end
        end

        if (failed_iside_accesses.exists(aligned_fetch_addr)) begin
          failed_iside_accesses.delete(aligned_fetch_addr);
        end
      end
    end
  endtask: run_cosim_ifetch

  task run_cosim_ifetch_pmp();
    ibex_ifetch_pmp_seq_item ifetch_pmp;

    // Keep track of which addresses have seen PMP failures.
    forever begin
      ifetch_pmp_port.get(ifetch_pmp);

      if (ifetch_pmp.fetch_pmp_err) begin
        iside_pmp_failure[ifetch_pmp.fetch_addr] = 1'b1;
      end else begin
        if (iside_pmp_failure.exists(ifetch_pmp.fetch_addr)) begin
          iside_pmp_failure.delete(ifetch_pmp.fetch_addr);
        end
      end
    end
  endtask

  task run_cosim_imem_errors();
    bit [63:0] latest_order = 64'hffffffff_ffffffff;
    bit [31:0] aligned_addr;
    bit [31:0] aligned_next_addr;
    forever begin
      // Wait for new instruction to appear in ID stage
      wait (instr_vif.instr_cb.valid_id &&
            instr_vif.instr_cb.instr_new_id &&
            latest_order != instr_vif.instr_cb.rvfi_order_id);

      latest_order = instr_vif.instr_cb.rvfi_order_id;

      if (dut_vif.dut_cb.wb_exception)
        // If an exception in writeback occurs the instruction in ID will be flushed and hence not
        // produce an iside error so skip the rest of the loop. A writeback exception may occur
        // after this cycle before the instruction in ID moves out of the ID stage. The
        // `run_cosim_prune_imem_errors` task deals with this case.
        continue;

      // Determine if the instruction comes from an address that has seen an error that wasn't a PMP
      // error (the icache records both PMP errors and fetch errors with the same error bits). If a
      // fetch error was seen add the instruction order ID and address to iside_error_queue.
      aligned_addr      = instr_vif.instr_cb.pc_id & 32'hfffffffc;
      aligned_next_addr = aligned_addr + 32'd4;

      if (failed_iside_accesses.exists(aligned_addr) && !iside_pmp_failure.exists(aligned_addr))
      begin
        iside_error_queue.push_back('{order : instr_vif.instr_cb.rvfi_order_id,
                                      addr  : aligned_addr});
        check_inserted_iside_error_e.trigger();
      end else if (!instr_vif.instr_cb.is_compressed_id &&
                   (instr_vif.instr_cb.pc_id & 32'h3) != 0 &&
                   failed_iside_accesses.exists(aligned_next_addr) &&
                   !iside_pmp_failure.exists(aligned_next_addr))
      begin
        // Where an instruction crosses a 32-bit boundary, check if an error was seen on the other
        // side of the boundary
        iside_error_queue.push_back('{order : instr_vif.instr_cb.rvfi_order_id,
                                      addr  : aligned_next_addr});
        check_inserted_iside_error_e.trigger();
      end

    end
  endtask: run_cosim_imem_errors;

  task run_cosim_prune_imem_errors();
    // Errors are added to the iside error queue the first cycle the instruction that sees the error
    // is in the ID stage. Cycles following this the writeback stage may cause an exception flushing
    // the ID stage so the iside error never occurs. When this happens we need to pop the new iside
    // error off the queue.
    forever begin
      // Wait until the `run_cosim_imem_errors` task notifies us it's added a error to the queue
      check_inserted_iside_error_e.wait_ptrigger();
      // Wait for the next clock
      @(instr_vif.instr_cb);
      // Wait for a new instruction or a writeback exception. When a new instruction has entered the
      // ID stage and we haven't seen a writeback exception we know the instruction associated with the
      // error just added to the queue isn't getting flushed.
      wait (instr_vif.instr_cb.instr_new_id || dut_vif.dut_cb.wb_exception);

      if (!instr_vif.instr_cb.instr_new_id && dut_vif.dut_cb.wb_exception) begin
        // If we hit a writeback exception without seeing a new instruction then the newly added
        // error relates to an instruction just flushed from the ID stage so pop it from the
        // queue.
        iside_error_queue.pop_back();
      end
    end
  endtask: run_cosim_prune_imem_errors

  function string get_cosim_error_str();
      string error = "Cosim mismatch ";
      for (int i = 0; i < riscv_cosim_get_num_errors(cosim_handle); ++i) begin
        error = {error, riscv_cosim_get_error(cosim_handle, i), "\n"};
      end
      riscv_cosim_clear_errors(cosim_handle);

      return error;
  endfunction : get_cosim_error_str

  function void final_phase(uvm_phase phase);
    super.final_phase(phase);

    `uvm_info(`gfn, $sformatf("Co-simulation matched %d instructions",
                                riscv_cosim_get_insn_cnt(cosim_handle)), UVM_LOW)

    cleanup_cosim();
  endfunction : final_phase

  // If the UVM_EXIT action is triggered (such as by reaching max_quit_count), this callback is run.
  // This ensures proper cleanup, such as commiting the logfile to disk.
  function void pre_abort();
    cleanup_cosim();
  endfunction

  task handle_reset();
    init_cosim();
  endtask
endclass : ibex_cosim_scoreboard
