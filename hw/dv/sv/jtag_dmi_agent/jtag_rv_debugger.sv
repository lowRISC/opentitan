// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class that provides common RISCV debugging utilities over JTAG.
//
// The utilities provided here allow the user to mimic an external debugger performing tasks such
// as halting the CPU, asserting a non-debug domain reset, accessing the CPU registers and memory
// using abstract commands, inserting breakpoints, single-stepping, causing the CPU to execute
// arbitrary instructions and accessing the chip resources over the SBA interface.
class jtag_rv_debugger extends uvm_object;
  `uvm_object_utils(jtag_rv_debugger)

  // A pre-created handle to the jtag_agent_cfg object.
  protected jtag_agent_cfg cfg;

  // A pre-created handle to the JTAG DMI reg block with a frontdoor accessor attached.
  protected jtag_dmi_reg_block ral;

  // Enable prediction on writes.
  bit predict_dmi_writes = 1;

  // Number of harts in the system. TODO: add support for multi-hart system.
  int num_harts = 1;

  // Indicates whether aarpostincrement is supported.
  bit aarpostincrement_supported;

  // An sba_access_reg_frontdoor instance to provide access to system CSRs via SBA using JTAG.
  sba_access_reg_frontdoor m_sba_access_reg_frontdoor;

  function new (string name = "");
    super.new(name);
    m_sba_access_reg_frontdoor = sba_access_reg_frontdoor::type_id::create(
        "m_sba_access_reg_frontdoor");
    m_sba_access_reg_frontdoor.debugger_h = this;
  endfunction : new

  // Sets the jtag_agent_cfg handle.
  virtual function void set_cfg(jtag_agent_cfg cfg);
    this.cfg = cfg;
  endfunction

  // Returns the jtag_agent_cfg handle.
  virtual function jtag_agent_cfg get_cfg();
    return cfg;
  endfunction

  // Sets the jtag_dmi_reg_block handle.
  virtual function void set_ral(jtag_dmi_reg_block ral);
    this.ral = ral;
  endfunction

  // Returns the jtag_dmi_reg_block handle.
  virtual function jtag_dmi_reg_block get_ral();
    return ral;
  endfunction

  // Asserts TRST_N for a few cycles.
  virtual task do_trst_n(int cycles = $urandom_range(5, 20));
    `uvm_info(`gfn, "Asserting TRST_N", UVM_MEDIUM)
    cfg.vif.do_trst_n(cycles);
  endtask

  // Enables the debug module.
  virtual task set_dmactive(bit value);
    `uvm_info(`gfn, $sformatf("Setting dmactive = %0b", value), UVM_MEDIUM)
    csr_wr(.ptr(ral.dmcontrol.dmactive), .value(value), .blocking(1), .predict(predict_dmi_writes));
  endtask

  // Issues a CPU halt request.
  virtual task set_haltreq(bit value, int hart = 0);
    `uvm_info(`gfn, $sformatf("Setting haltreq = %0b", value), UVM_MEDIUM)
    csr_wr(.ptr(ral.dmcontrol.haltreq), .value(value), .blocking(1), .predict(predict_dmi_writes));
  endtask

  // Waits for the CPU to be in halted state.
  virtual task wait_cpu_halted(int hart = 0);
    uvm_reg_data_t data;
    `uvm_info(`gfn, "Waiting for CPU halted", UVM_MEDIUM)
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.dmstatus), .value(data), .blocking(1));
      end while (dv_base_reg_pkg::get_field_val(ral.dmstatus.anyhalted, data) == 0);
    )
    if (num_harts == 1) begin
      `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(ral.dmstatus.allhalted, data), 1)
    end
    `uvm_info(`gfn, "Done waiting for CPU halted", UVM_MEDIUM)
  endtask

  // Issues an NDM reset request.
  virtual task set_ndmreset(bit value);
    `uvm_info(`gfn, $sformatf("Setting ndmreset = %0b", value), UVM_MEDIUM)
    csr_wr(.ptr(ral.dmcontrol.ndmreset), .value(value), .blocking(1), .predict(predict_dmi_writes));
  endtask

  // Issues a CPU resume reset request.
  virtual task set_resumereq(bit value);
    `uvm_info(`gfn, $sformatf("Setting resumereq = %0b", value), UVM_MEDIUM)
    csr_wr(.ptr(ral.dmcontrol.resumereq), .value(value), .blocking(1),
           .predict(predict_dmi_writes));
  endtask

  // Checks if we are ready for executing abstract commands.
  //
  // Recommended to be run once at the very start of the debug session.
  // ready: Returns whether the debug module is ready to accept abstract commands.
  virtual task abstract_cmd_dm_ready(output bit ready);
    uvm_reg_data_t data;
    csr_rd(.ptr(ral.dmcontrol), .value(data), .blocking(1));
    ready = 1;
    ready &= dv_base_reg_pkg::get_field_val(ral.dmcontrol.dmactive, data) == 1;
    ready &= dv_base_reg_pkg::get_field_val(ral.dmcontrol.ackhavereset, data) == 0;
    ready &= dv_base_reg_pkg::get_field_val(ral.dmcontrol.resumereq, data) == 0;
    ready &= dv_base_reg_pkg::get_field_val(ral.dmcontrol.haltreq, data) == 0;
    csr_rd(.ptr(ral.dmstatus), .value(data), .blocking(1));
    ready &= dv_base_reg_pkg::get_field_val(ral.dmstatus.allhalted, data) == 1;
    csr_rd(.ptr(ral.abstractcs), .value(data), .blocking(1));
    ready &= dv_base_reg_pkg::get_field_val(ral.abstractcs.busy, data) == 0;
    ready &= dv_base_reg_pkg::get_field_val(ral.abstractcs.cmderr, data) == AbstractCmdErrNone;
  endtask

  // Waits for an abstract cmd to finish executing.
  //
  // status: Returns the status of the previous executed command.
  // cmderr_clear: Clear the cmd error status (default off).
  virtual task abstract_cmd_busy_wait(output abstract_cmd_err_e status,
                                      input  bit cmderr_clear = 0);
    uvm_reg_data_t data;
    `uvm_info(`gfn, "Waiting for an abstract command (if any) to complete execution", UVM_MEDIUM)
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.abstractcs), .value(data), .blocking(1));
      end while (dv_base_reg_pkg::get_field_val(ral.abstractcs.busy, data) == 1);
    )
    status = abstract_cmd_err_e'(dv_base_reg_pkg::get_field_val(ral.abstractcs.cmderr, data));
    if (status != AbstractCmdErrNone && cmderr_clear) begin
      csr_wr(.ptr(ral.abstractcs.cmderr), .value(1), .blocking(1), .predict(predict_dmi_writes));
    end
  endtask

  // Disables the abstract cmd by setting the control field to 0.
  virtual task abstract_cmd_disable();
    uvm_reg_data_t rw_data = '0;
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.cmdtype, rw_data,
                                                            AbstractCmdRegAccess);
    csr_wr(.ptr(ral.command), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));
  endtask

  // Writes the abstractauto register to enable automatic command execution.
  //
  // The default value for the args are set to 0 to prioritize disabling of the autoexec feature.
  virtual task write_abstract_cmd_auto(bit autoexecdata = 0, bit autoexecprogbuf = 0);
    uvm_reg_data_t rw_data = '0;
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(
        ral.abstractauto.autoexecprogbuf, rw_data, autoexecprogbuf);
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(
        ral.abstractauto.autoexecdata, rw_data, autoexecdata);
    csr_wr(.ptr(ral.abstractauto), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));
  endtask

  // Reads (a) CPU register(s) via an abstract command.
  //
  // regno: The starting CPU register number.
  // value_q: A queue of returned reads.
  // size: The Number of successive reads. The regno is incremented this many times.
  // postexec: Have the CPU execute the progbuf immediately after the command.
  // progbuf_q: A new set of arbitrary commands.
  // TODO: add support for sub-word transfer size.
  virtual task abstract_cmd_reg_read(input abstract_cmd_regno_t regno,
                                     output logic [BUS_DW-1:0] value_q[$],
                                     output abstract_cmd_err_e status,
                                     input int size = 1,
                                     input bit postexec = 0,
                                     input logic [BUS_DW-1:0] progbuf_q[$] = {});
    uvm_reg_data_t rw_data = '0;
    abstract_cmd_reg_access_t cmd = '0;

    if (postexec) write_progbuf(progbuf_q);
    if (aarpostincrement_supported && size > 1) begin
      write_abstract_cmd_auto(.autoexecdata(1));
      cmd.aarpostincrement = 1;
    end

    cmd.aarsize = 2;
    cmd.postexec = postexec;
    cmd.transfer = 1;
    cmd.regno = regno;
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.cmdtype, rw_data,
                                                            AbstractCmdRegAccess);
    if (aarpostincrement_supported) begin
      // Write command only once at the start.
      rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.control, rw_data,
                                                              cmd);
      csr_wr(.ptr(ral.command), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));
    end

    for (int i = 0; i < size; i++) begin
      if (!aarpostincrement_supported) begin
        // Manually increment regno and write command for each read.
        cmd.regno = regno + i;
        rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.control, rw_data,
                                                                cmd);
        csr_wr(.ptr(ral.command), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));
      end
      abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
      // Let the caller handle error cases.
      if (status != AbstractCmdErrNone) return;
      // Before the last read, reset the autoexecdata bit.
      if (aarpostincrement_supported && size > 1 && i == size - 1) write_abstract_cmd_auto();
      csr_rd(.ptr(ral.abstractdata[0]), .value(value_q[i]), .blocking(1));
    end
  endtask

  // Writes (a) CPU register(s) via an abstract command.
  //
  // regno: The starting CPU register number.
  // value_q: A queue of data written. regno is incremented for each value.
  // size: The Number of successive reads.
  // postexec: Have the CPU execute the progbuf immediately after the command.
  // progbuf_q: A new set of arbitrary commands.
  virtual task abstract_cmd_reg_write(input abstract_cmd_regno_t regno,
                                      input logic [BUS_DW-1:0] value_q[$],
                                      output abstract_cmd_err_e status,
                                      input bit postexec = 0,
                                      input logic [BUS_DW-1:0] progbuf_q[$] = {});
    uvm_reg_data_t rw_data = '0;
    abstract_cmd_reg_access_t cmd = '0;

    if (postexec) write_progbuf(progbuf_q);
    csr_wr(.ptr(ral.abstractdata[0]), .value(value_q[0]), .blocking(1),
           .predict(predict_dmi_writes));

    cmd.aarsize = 2;
    cmd.postexec = postexec;
    cmd.transfer = 1;
    cmd.write = 1;
    cmd.regno = regno;
    cmd.aarpostincrement = aarpostincrement_supported && (value_q.size() > 1);
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.cmdtype, rw_data,
                                                            AbstractCmdRegAccess);
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.control, rw_data,
                                                            cmd);
    csr_wr(.ptr(ral.command), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));

    if (aarpostincrement_supported && (value_q.size() > 1)) begin
      write_abstract_cmd_auto(.autoexecdata(1));
    end

    for (int i = 1; i < value_q.size(); i++) begin
      abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
      // Let the caller handle error cases.
      if (status != AbstractCmdErrNone) return;
      csr_wr(.ptr(ral.abstractdata[0]), .value(value_q[i]), .blocking(1),
             .predict(predict_dmi_writes));
      if (!aarpostincrement_supported) begin
        // Manually increment regno and write command for each write.
        cmd.regno = regno + i;
        rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.control, rw_data,
                                                                cmd);
        csr_wr(.ptr(ral.command), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));
      end
    end
    abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
    // After the last write, reset the autoexecdata bit.
    if (aarpostincrement_supported && (value_q.size() > 1)) write_abstract_cmd_auto();
  endtask

  // Reads (a) memory location(s) via an abstract command.
  virtual task abstract_cmd_mem_read(input logic [BUS_AW-1:0] addr,
                                     output logic [BUS_DW-1:0] value_q[$],
                                     output abstract_cmd_err_e status,
                                     input int size = 1,
                                     input bit postexec = 0,
                                     input logic [BUS_DW-1:0] progbuf_q[$] = {});
    `uvm_fatal(`gfn, "Not implemented")
  endtask

  // Writes (a) memory location(s) via an abstract command.
  virtual task abstract_cmd_mem_write(input logic [BUS_AW-1:0] addr,
                                      input logic [BUS_DW-1:0] value_q[$],
                                      output abstract_cmd_err_e status,
                                      input bit postexec = 0,
                                      input logic [BUS_DW-1:0] progbuf_q[$] = {});
    `uvm_fatal(`gfn, "Not implemented")
  endtask

  // Issue a quick access command.
  virtual task abstract_cmd_quick_access(output abstract_cmd_err_e status,
                                         input logic [BUS_DW-1:0] progbuf_q[$] = {});
    uvm_reg_data_t rw_data = '0;
    // TODO: Check if core is not halted.
    write_progbuf(progbuf_q);
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.cmdtype, rw_data,
                                                            AbstractCmdQuickAccess);
    csr_wr(.ptr(ral.command), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));
    abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
    // Note: The external testbench is expected to check the CPU automatically halted, executed the
    // progbuf and then, resumed.
  endtask

  // Have the CPU execute arbitrary instructions in the program buffer.
  virtual task abstract_cmd_exec_progbuf(input logic [BUS_DW-1:0] progbuf_q[$],
                                         output abstract_cmd_err_e status);
    uvm_reg_data_t rw_data = '0;
    abstract_cmd_reg_access_t cmd = '0;

    write_progbuf(progbuf_q);
    cmd.postexec = 1;
    cmd.transfer = 0;
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.cmdtype, rw_data,
                                                            AbstractCmdRegAccess);
    rw_data = csr_utils_pkg::get_csr_val_with_updated_field(ral.command.control, rw_data,
                                                            cmd);
    csr_wr(.ptr(ral.command), .value(rw_data), .blocking(1), .predict(predict_dmi_writes));
    abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
  endtask

 // Issue a quick access command.
  virtual task abstract_cmd_custom(/* abstract_cmd_item req*/);
    `uvm_fatal(`gfn, "Not implemented")
  endtask

  // Write arbitrary commands into progbuf.
  virtual task write_progbuf(logic [BUS_DW-1:0] progbuf_q[$]);
    `DV_CHECK_LE_FATAL(progbuf_q.size(), ral.abstractcs.progbufsize.get())
    foreach (progbuf_q[i]) begin
      csr_wr(.ptr(ral.progbuf[i]), .value(progbuf_q[i]), .blocking(1),
             .predict(predict_dmi_writes));
    end
  endtask

  // Insert a breakpoint.
  virtual task insert_breakpoint();
  endtask

  // Single step.
  virtual task step(int num = 1);
    // Write step bit in dcsr.
    // Assert resumereq.
  endtask

  // Initiates a single SBA access through JTAG (-> DTM -> DMI -> SBA).
  //
  // It writes DMI SBA registers to create a read or write access on the system bus, poll for its
  // completion and return the response (on reads).
  //
  // req: The SBA access request item. It will be updated with the responses.
  // sba_access_err_clear: Knob to clear the SBA access errors.
  virtual task sba_access(sba_access_item req, bit sba_access_err_clear = 1'b1);
    uvm_reg_data_t rdata, wdata;

    // Update sbcs for the new transaction.
    wdata = ral.sbcs.get_mirrored_value();
    wdata = get_csr_val_with_updated_field(ral.sbcs.sbaccess, wdata, req.size);
    if (req.bus_op == BusOpRead) begin
      wdata = get_csr_val_with_updated_field(ral.sbcs.sbreadonaddr, wdata, req.readonaddr);
      wdata = get_csr_val_with_updated_field(ral.sbcs.sbreadondata, wdata, req.readondata);
    end else begin
      // If we set these bits on writes, it complicates things.
      wdata = get_csr_val_with_updated_field(ral.sbcs.sbreadonaddr, wdata, 0);
      wdata = get_csr_val_with_updated_field(ral.sbcs.sbreadondata, wdata, 0);
    end
    wdata = get_csr_val_with_updated_field(ral.sbcs.sbautoincrement, wdata,
                                           (req.autoincrement > 0));
    if (wdata != ral.sbcs.sbaccess.get_mirrored_value()) begin
      csr_wr(.ptr(ral.sbcs), .value(wdata), .blocking(1), .predict(predict_dmi_writes));
    end

    // Update the sbaddress0.
    csr_wr(.ptr(ral.sbaddress0), .value(req.addr), .blocking(1), .predict(predict_dmi_writes));

    // These steps are run in several branches in the following code. Macroize them.
    `define BUSYWAIT_AND_EXIT_ON_ERR                                                            \
        sba_access_busy_wait_and_clear_error(.req(req),                                         \
            .sba_access_err_clear(sba_access_err_clear));                                       \
                                                                                                \
        // We don't know what to do if any of the following is true - return to the caller:     \
        //                                                                                      \
        // - The request timed out or returned is_busy_err                                      \
        // - The access reported non-0 sberror and sba_access_err_clear is set to 0             \
        // - Request was malformed (An SBA access is not made in the case)                      \
        // - The access returned SbaErrOther error response (The DUT may need special handling) \
        if (req.timed_out ||                                                                    \
            req.is_busy_err ||                                                                  \
            (req.is_err != SbaErrNone && !sba_access_err_clear) ||                              \
            req.is_err inside {SbaErrBadAlignment, SbaErrBadSize, SbaErrOther}) begin           \
          return;                                                                               \
        end                                                                                     \

    // Write / read sbdata, wait for transaction to complete.
    if (req.bus_op == BusOpRead) begin
      case ({req.readondata, req.readonaddr})
        2'b00: begin
          // No SBA read will be triggered. Read sbdata0 and and check status anyway (25% of the
          // time). The external scoreboard is expected to verify that no SBA transaction is seen.
          if (!cfg.in_reset && !$urandom_range(0, 3)) begin  // 25%
            csr_rd(.ptr(ral.sbdata0), .value(rdata), .blocking(1));
            `BUSYWAIT_AND_EXIT_ON_ERR
          end
        end
        2'b01: begin
          // SBA read already triggered on write to sbaddress0. Read sbdata0 to fetch the response
          // data. If autoincrement is set, then return to the caller - it is not a valid usecase.
          `BUSYWAIT_AND_EXIT_ON_ERR
          if (!cfg.in_reset) begin
            csr_rd(.ptr(ral.sbdata0), .value(rdata), .blocking(1));
            req.rdata[0] = rdata;
          end
        end
        2'b10, 2'b11: begin
          if (!req.readonaddr) begin
            // The first read to sbdata returns stale data. Discard it.
            if (!cfg.in_reset) begin
              csr_rd(.ptr(ral.sbdata0), .value(rdata), .blocking(1));
            end
          end

          // Read sbdata req.autoincrement+1 number of times.
          //
          // Randomly also inject reads to sbaddress0 to verify address is correctly incremented
          // (checked by sba_access_monitor or the external scoreboard).
          for (int i = 0; i < req.autoincrement + 1; i++) begin
            // The previous step triggered an SBA read. Wait for it to complete.
            `BUSYWAIT_AND_EXIT_ON_ERR
            if (!cfg.in_reset && i > 0 && !$urandom_range(0, 3)) begin  //25%
              csr_rd(.ptr(ral.sbaddress0), .value(rdata));
            end
            // Before the last read, set readondata to 0 to prevent new SBA read triggers.
            if (!cfg.in_reset && i == req.autoincrement) begin
              wdata = get_csr_val_with_updated_field(ral.sbcs.sbreadondata, wdata, 0);
              csr_wr(.ptr(ral.sbcs), .value(wdata), .blocking(1), .predict(predict_dmi_writes));
            end
            if (!cfg.in_reset) begin
              csr_rd(.ptr(ral.sbdata0), .value(rdata));
              req.rdata[i] = rdata;
            end
          end
        end
        default: begin
          `uvm_fatal(`gfn, "Unreachable!")
        end
      endcase
    end else begin
      // Write sbdata req.autoincrement+1 number of times.
      //
      // Randomly also inject reads to sbaddress0 to verify address is correctly incremented
      // (done externally by the scoreboard).
      for (int i = 0; i < req.autoincrement + 1; i++) begin
        if (!cfg.in_reset) begin
          csr_wr(.ptr(ral.sbdata0), .value(req.wdata[i]), .blocking(1),
                 .predict(predict_dmi_writes));
        end
        `BUSYWAIT_AND_EXIT_ON_ERR
        if (i > 0 && !cfg.in_reset && !$urandom_range(0, 3)) begin  //25%
          csr_rd(.ptr(ral.sbaddress0), .value(rdata), .blocking(1));
        end
      end
    end

  `undef BUSYWAIT_AND_EXIT_ON_ERR
  endtask

  // Read the SBA access status.
  virtual task sba_access_status(input sba_access_item req, output logic is_busy);
    uvm_reg_data_t data;
    csr_rd(.ptr(ral.sbcs), .value(data), .blocking(1));
    is_busy = get_field_val(ral.sbcs.sbbusy, data);
    req.is_busy_err = get_field_val(ral.sbcs.sbbusyerror, data);
    req.is_err = sba_access_err_e'(get_field_val(ral.sbcs.sberror, data));
    if (!is_busy) begin
      `uvm_info(`gfn, $sformatf("SBA req completed: %0s", req.sprint(uvm_default_line_printer)),
                UVM_HIGH)
    end
  endtask

  // Reads sbcs register to poll and wait for access to complete.
  virtual task sba_access_busy_wait(input sba_access_item req);
    logic is_busy;
    `DV_SPINWAIT_EXIT(
      do begin
        sba_access_status(req, is_busy);
        if (req.is_err != SbaErrNone) `DV_CHECK_EQ(is_busy, 0)
      end while (is_busy && !req.is_busy_err);,
      begin
        fork
          // TODO: Provide callbacks to support waiting for custom exit events.
          wait(cfg.in_reset);
          begin
            // TODO: Make this timeout controllable.
            #(cfg.vif.tck_period_ns * 100000 * 1ns);
            req.timed_out = 1'b1;
            `uvm_info(`gfn, $sformatf("SBA req timed out: %0s",
                                      req.sprint(uvm_default_line_printer)), UVM_LOW)
          end
        join_any
      end
    )
  endtask

  // Clear SBA access busy error and access error sticky bits if they are set.
  //
  // Note that the req argument will continue to reflect the error bits.
  virtual task sba_access_error_clear(sba_access_item req, bit clear_sbbusyerror = 1'b1,
                                      bit clear_sberror = 1'b1);
    uvm_reg_data_t data = ral.sbcs.get_mirrored_value();
    if (clear_sbbusyerror && req.is_busy_err) begin
      data = get_csr_val_with_updated_field(ral.sbcs.sbbusyerror, data, 1);
    end
    if (clear_sberror && req.is_err != SbaErrNone) begin
      data = get_csr_val_with_updated_field(ral.sbcs.sberror, data, 1);
    end
    csr_wr(.ptr(ral.sbcs), .value(data), .blocking(1), .predict(predict_dmi_writes));
  endtask

  // Wrapper task for busy wait followed by clearing of sberror if an error was reported.
  virtual task sba_access_busy_wait_and_clear_error(sba_access_item req, bit sba_access_err_clear);
    sba_access_busy_wait(req);
    // Only clear sberror - let the caller handle sbbusyerror.
    if (!cfg.in_reset && sba_access_err_clear && req.is_err != SbaErrNone) begin
      sba_access_error_clear(.req(req), .clear_sbbusyerror(0));
    end
  endtask

  // Simplified version of sba_access(), for 32-bit reads.
  virtual task sba_read(input logic [BUS_AW-1:0] addr,
                        output logic [BUS_DW-1:0] value[$],
                        output sba_access_err_e status,
                        input int size = 1);
    sba_access_item sba_item = sba_access_item::type_id::create("sba_item");
    sba_item.bus_op = BusOpRead;
    sba_item.addr = addr;
    sba_item.size = SbaAccessSize32b;
    sba_item.autoincrement = size > 1 ? size : 0;
    sba_item.readonaddr = size == 1;
    sba_item.readondata = size > 1;
    sba_access(sba_item);
    `DV_CHECK_EQ(sba_item.rdata.size(), size)
    value = sba_item.rdata;
    status = sba_item.is_err;
    `DV_CHECK(!sba_item.is_busy_err)
    `DV_CHECK(!sba_item.timed_out)
  endtask

  // Simplified version of sba_access(), for 32-bit writes.
  virtual task sba_write(input logic [BUS_AW-1:0] addr,
                         input logic [BUS_DW-1:0] value[$],
                         output sba_access_err_e status);
    sba_access_item sba_item = sba_access_item::type_id::create("sba_item");
    sba_item.bus_op = BusOpWrite;
    sba_item.addr = addr;
    sba_item.wdata = value;
    sba_item.size = SbaAccessSize32b;
    sba_item.autoincrement = value.size() > 1 ? value.size() : 0;
    sba_access(sba_item);
    status = sba_item.is_err;
    `DV_CHECK(!sba_item.is_busy_err)
    `DV_CHECK(!sba_item.timed_out)
  endtask

endclass
