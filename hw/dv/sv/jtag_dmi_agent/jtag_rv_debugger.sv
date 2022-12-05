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

  // The elf file executed by the CPU.
  protected string elf_file;

  // Enable prediction on writes.
  bit predict_dmi_writes = 1;

  // Number of harts in the system. TODO: add support for multi-hart system.
  int num_harts = 1;

  // Number of breakpoints (triggers) supported.
  int num_triggers;

  // Indicates whether aarpostincrement is supported.
  bit aarpostincrement_supported;

  // An sba_access_reg_frontdoor instance to provide access to system CSRs via SBA using JTAG.
  sba_access_reg_frontdoor m_sba_access_reg_frontdoor;

  // Internal status signals to optimize debugger performance.
  // TODO: Use these bits effectively.
  protected bit dmactive_is_set;
  protected bit cpu_is_halted;
  protected bit step_entered;
  protected logic [BUS_AW-1:0] symbol_table[string];

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

  // Sets the elf file name.
  virtual function void set_elf_file(string elf_file);
    this.elf_file = elf_file;
    symbol_table.delete();
  endfunction

  // Returns the elf file name.
  virtual function string get_elf_file();
    return elf_file;
  endfunction

  // Asserts TRST_N for a few cycles.
  virtual task do_trst_n(int cycles = $urandom_range(5, 20));
    `uvm_info(`gfn, "Asserting TRST_N", UVM_MEDIUM)
    cfg.vif.do_trst_n(cycles);
    dmactive_is_set = 0;
    cpu_is_halted = 0;
    step_entered = 0;
  endtask

  // Enables the debug module.
  virtual task set_dmactive(bit value);
    `uvm_info(`gfn, $sformatf("Setting dmactive = %0b", value), UVM_MEDIUM)
    csr_wr(.ptr(ral.dmcontrol.dmactive), .value(value), .blocking(1), .predict(predict_dmi_writes));
    dmactive_is_set = value;
    if (!value) begin
      cpu_is_halted = 0;
      step_entered = 0;
    end
  endtask

  // Issues a CPU halt request.
  virtual task set_haltreq(bit value, int hart = 0);
    `uvm_info(`gfn, $sformatf("Setting haltreq = %0b", value), UVM_MEDIUM)
    csr_wr(.ptr(ral.dmcontrol.haltreq), .value(value), .blocking(1), .predict(predict_dmi_writes));
  endtask

  // Waits for the CPU to be in halted state.
  virtual task wait_cpu_halted(int hart = 0);
    uvm_reg_data_t data;
    `uvm_info(`gfn, "Waiting for CPU to halt", UVM_MEDIUM)
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.dmstatus), .value(data), .blocking(1));
      end while (dv_base_reg_pkg::get_field_val(ral.dmstatus.anyhalted, data) == 0);
    )
    if (num_harts == 1) begin
      `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(ral.dmstatus.allhalted, data), 1)
    end
    `uvm_info(`gfn, "CPU has halted", UVM_MEDIUM)
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

  // Waits for the CPU to be in resumed state.
  virtual task wait_cpu_resumed(int hart = 0);
    uvm_reg_data_t data;
    `uvm_info(`gfn, "Waiting for CPU to resume", UVM_MEDIUM)
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(ral.dmstatus), .value(data), .blocking(1));
      end while (dv_base_reg_pkg::get_field_val(ral.dmstatus.anyhalted, data) == 1);
    )
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(ral.dmstatus.anyrunning, data), 1)
    if (num_harts == 1) begin
      `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(ral.dmstatus.allhalted, data), 0)
      `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(ral.dmstatus.allrunning, data), 1)
    end
    `uvm_info(`gfn, "CPU has resumed", UVM_MEDIUM)
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
    `uvm_info(`gfn, "Abstract command completed", UVM_MEDIUM)
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
  // postexec: Have the CPU execute the progbuf immediately after the command. The progbuf is
  // assumed to have been loaded already.
  // TODO: add support for sub-word transfer size.
  // TODO: Add support for reg read via program buffer.
  virtual task abstract_cmd_reg_read(input abstract_cmd_regno_t regno,
                                     output logic [BUS_DW-1:0] value_q[$],
                                     output abstract_cmd_err_e status,
                                     input int size = 1,
                                     input bit postexec = 0);
    uvm_reg_data_t rw_data = '0;
    abstract_cmd_reg_access_t cmd = '0;

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
      `uvm_info(`gfn, $sformatf("Read CPU register 0x%0h: 0x%0h", regno + i, value_q[i]),
                UVM_MEDIUM)
    end
  endtask

  // Writes (a) CPU register(s) via an abstract command.
  //
  // regno: The starting CPU register number.
  // value_q: A queue of data written. regno is incremented for each value.
  // size: The Number of successive reads.
  // postexec: Have the CPU execute the progbuf immediately after the command. The progbuf is
  // assumed to have been loaded already.
  // TODO: Add support for reg read via program buffer.
  virtual task abstract_cmd_reg_write(input abstract_cmd_regno_t regno,
                                      input logic [BUS_DW-1:0] value_q[$],
                                      output abstract_cmd_err_e status,
                                      input bit postexec = 0);
    uvm_reg_data_t rw_data = '0;
    abstract_cmd_reg_access_t cmd = '0;

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
    `uvm_info(`gfn, $sformatf("Wrote 0x%0h to CPU register 0x%0h", value_q[0], cmd.regno),
              UVM_MEDIUM)

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
      `uvm_info(`gfn, $sformatf("Wrote 0x%0h to CPU register 0x%0h", value_q[i], regno + i),
                UVM_MEDIUM)
    end
    abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
    // After the last write, reset the autoexecdata bit.
    if (aarpostincrement_supported && (value_q.size() > 1)) write_abstract_cmd_auto();
  endtask

  // Reads (a) system memory location(s) via an abstract command.
  //
  // The system memory address space can be accessed either via `AbstractCmdMemAccess` abstract
  // command type, or indirectly using the CPU using the program buffer. The former is not currently
  // supported.
  // addr: The starting system address.
  // value_q: The read data returned to the caller.
  // status: The status of the op returned to the caller.
  // size: The size of the read access in terms of full bus words.
  // route: The route taken to access the system memory.
  virtual task abstract_cmd_mem_read(input logic [BUS_AW-1:0] addr,
                                     output logic [BUS_DW-1:0] value_q[$],
                                     output abstract_cmd_err_e status,
                                     input int size = 1,
                                     input mem_access_route_e route = MemAccessViaProgbuf);
    `DV_CHECK(size)
    case (route)
      MemAccessViaAbstractCmd: begin
        `uvm_fatal(`gfn, "Accessing the system memory using AbstractCmdMemAccess is not supproted")
      end
      MemAccessViaProgbuf: begin
        logic [BUS_DW-1:0] progbuf_q[$];
        logic [BUS_DW-1:0] rwdata[$];
        logic [BUS_DW-1:0] s0, s1;

        if (size == 1) progbuf_q = '{LwS0S0, Ebreak};
        else progbuf_q = '{LwS1S0, AddiS0S04, Ebreak};

        abstract_cmd_reg_read(.regno(RvCoreCsrGprS0), .value_q(rwdata), .status(status));
        if (status != AbstractCmdErrNone) return;
        s0 = rwdata[0];
        if (size > 1) begin
          abstract_cmd_reg_read(.regno(RvCoreCsrGprS1), .value_q(rwdata), .status(status));
          if (status != AbstractCmdErrNone) return;
          s1 = rwdata[0];
        end
        `uvm_info(`gfn, $sformatf("Saved CPU registers S0 = 0x%0h and S1 = 0x%0h",  s0, s1),
                  UVM_HIGH)

        value_q.delete();
        write_progbuf(progbuf_q);
        abstract_cmd_reg_write(.regno(RvCoreCsrGprS0), .value_q({addr}), .status(status),
                               .postexec(1));
        if (status != AbstractCmdErrNone) return;
        abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
        if (status != AbstractCmdErrNone) return;
        if (size == 1) begin
          abstract_cmd_reg_read(.regno(RvCoreCsrGprS0), .value_q(value_q), .status(status));
          if (status != AbstractCmdErrNone) return;
        end else begin
          abstract_cmd_reg_read(.regno(RvCoreCsrGprS1), .value_q(rwdata), .status(status),
                                .postexec(1));
          if (status != AbstractCmdErrNone) return;
          value_q[0] = rwdata[0];
          `uvm_info(`gfn, $sformatf("Read from system memory: [0x%0h] = 0x%0h", addr,
                                    value_q[0]), UVM_MEDIUM)
          write_abstract_cmd_auto(.autoexecdata(1));
          for (int i = 1; i < size; i++) begin
            abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
            if (status != AbstractCmdErrNone) return;
            // Before the last read, reset the autoexecdata bit.
            if (i == size - 1) write_abstract_cmd_auto();
            csr_rd(.ptr(ral.abstractdata[0]), .value(value_q[i]), .blocking(1));
            `uvm_info(`gfn, $sformatf("Read from system memory: [0x%0h] = 0x%0h", addr + i * 4,
                                      value_q[i]), UVM_MEDIUM)
          end
        end

        abstract_cmd_reg_write(.regno(RvCoreCsrGprS0), .value_q({s0}), .status(status));
        if (status != AbstractCmdErrNone) return;
        if (size > 1) begin
          abstract_cmd_reg_write(.regno(RvCoreCsrGprS1), .value_q({s1}), .status(status));
          if (status != AbstractCmdErrNone) return;
        end
        `uvm_info(`gfn, $sformatf("Restored CPU registers S0 = 0x%0h and S1 = 0x%0h",  s0, s1),
                  UVM_HIGH)
      end
      MemAccessViaSba: begin
        `uvm_fatal(`gfn, "Please invoke sba_read instead")
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("The mem access route %s is invalid or unsupported",
                                   route.name()))
      end
    endcase
  endtask

  // Writes (a) system memory location(s) via an abstract command.
  //
  // The system memory address space can be accessed either via `AbstractCmdMemAccess` abstract
  // command type, or indirectly using the CPU using the program buffer. The former is not currently
  // supported.
  // addr: The starting system address.
  // value_q: The data set to be written.
  // status: The status of the op returned to the caller.
  // route: The route taken to access the system memory.
  virtual task abstract_cmd_mem_write(input logic [BUS_AW-1:0] addr,
                                      input logic [BUS_DW-1:0] value_q[$],
                                      output abstract_cmd_err_e status,
                                      input mem_access_route_e route = MemAccessViaProgbuf);
    `DV_CHECK(value_q.size())
    case (route)
      MemAccessViaAbstractCmd: begin
        `uvm_fatal(`gfn, "Accessing the system memory using AbstractCndMemAccess is not supproted")
      end
      MemAccessViaProgbuf: begin
        logic [BUS_DW-1:0] progbuf_q[$];
        logic [BUS_DW-1:0] rwdata[$];
        logic [BUS_DW-1:0] s0, s1;

        if (value_q.size() == 1) progbuf_q = '{SwS1S0, Ebreak};
        else progbuf_q = '{SwS1S0, AddiS0S04, Ebreak};

        abstract_cmd_reg_read(.regno(RvCoreCsrGprS0), .value_q(rwdata), .status(status));
        if (status != AbstractCmdErrNone) return;
        s0 = rwdata[0];
        abstract_cmd_reg_read(.regno(RvCoreCsrGprS1), .value_q(rwdata), .status(status));
        if (status != AbstractCmdErrNone) return;
        s1 = rwdata[0];
        `uvm_info(`gfn, $sformatf("Saved CPU registers S0 = 0x%0h and S1 = 0x%0h",  s0, s1),
                  UVM_HIGH)

        write_progbuf(progbuf_q);
        abstract_cmd_reg_write(.regno(RvCoreCsrGprS0), .value_q({addr}), .status(status));
        if (status != AbstractCmdErrNone) return;
        abstract_cmd_reg_write(.regno(RvCoreCsrGprS1), .value_q({value_q[0]}), .status(status),
                               .postexec(1));
        if (status != AbstractCmdErrNone) return;
        `uvm_info(`gfn, $sformatf("Wrote to system memory: [0x%0h] = 0x%0h", addr, value_q[0]),
                  UVM_MEDIUM)
        if (value_q.size() > 1) begin
          write_abstract_cmd_auto(.autoexecdata(1));
          for (int i = 1; i < value_q.size(); i++) begin
            csr_wr(.ptr(ral.abstractdata[0]), .value(value_q[i]), .blocking(1),
                   .predict(predict_dmi_writes));
            abstract_cmd_busy_wait(.status(status), .cmderr_clear(1));
            if (status != AbstractCmdErrNone) return;
            `uvm_info(`gfn, $sformatf("Wrote to system memory: [0x%0h] = 0x%0h", addr + i * 4,
                                      value_q[i]), UVM_MEDIUM)
          end
          write_abstract_cmd_auto();
        end

        abstract_cmd_reg_write(.regno(RvCoreCsrGprS0), .value_q({s0}), .status(status));
        if (status != AbstractCmdErrNone) return;
        abstract_cmd_reg_write(.regno(RvCoreCsrGprS1), .value_q({s1}), .status(status));
        if (status != AbstractCmdErrNone) return;
        `uvm_info(`gfn, $sformatf("Restored CPU registers S0 = 0x%0h and S1 = 0x%0h",  s0, s1),
                  UVM_HIGH)
      end
      MemAccessViaSba: begin
        `uvm_fatal(`gfn, "Please invoke sba_write instead")
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("The mem access route %s is invalid or unsupported",
                                   route.name()))
      end
    endcase
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

  // Write arbitrary commands into progbuf.
  virtual task write_progbuf(logic [BUS_DW-1:0] progbuf_q[$]);
    `DV_CHECK_LE_FATAL(progbuf_q.size(), ral.abstractcs.progbufsize.get())
    foreach (progbuf_q[i]) begin
      csr_wr(.ptr(ral.progbuf[i]), .value(progbuf_q[i]), .blocking(1),
             .predict(predict_dmi_writes));
    end
    `uvm_info(`gfn, $sformatf("Wrote progbuf: %p", progbuf_q), UVM_MEDIUM)
  endtask

  // Returns the saved PC via DPC register.
  virtual task read_pc(output logic [BUS_DW-1:0] pc);
    abstract_cmd_err_e status;
    logic [BUS_DW-1:0] cmd_data[$];
    abstract_cmd_reg_read(.regno(RvCoreCsrDpc), .value_q(cmd_data), .status(status));
    `DV_CHECK_EQ(status, AbstractCmdErrNone)
    `uvm_info(`gfn, $sformatf("DPC = 0x%0h", cmd_data[0]), UVM_LOW)
    pc = cmd_data[0];
  endtask

  // Set PC to a new value with address or the symbol
  virtual task write_pc(logic [BUS_AW-1:0] addr = 'x, string symbol = "");
    abstract_cmd_err_e status;
    logic [BUS_DW-1:0] cmd_data[$];

    addr_or_symbol_set(addr, symbol);
    abstract_cmd_reg_write(.regno(RvCoreCsrDpc), .value_q({addr}), .status(status));
    `DV_CHECK_EQ(status, AbstractCmdErrNone)
    `uvm_info(`gfn, $sformatf("Wrote new DPC = 0x%0h", addr), UVM_LOW)
  endtask

  // Returns the DCSR value.
  virtual task read_dcsr(output rv_core_csr_dcsr_t dcsr);
    abstract_cmd_err_e status;
    logic [BUS_DW-1:0] cmd_data[$];
    abstract_cmd_reg_read(.regno(RvCoreCsrDcsr), .value_q(cmd_data), .status(status));
    `DV_CHECK_EQ(status, AbstractCmdErrNone)
    dcsr = rv_core_csr_dcsr_t'(cmd_data[0]);
    `uvm_info(`gfn, $sformatf("DCSR = %p", dcsr), UVM_MEDIUM)
  endtask

  // Set the DCSR value.
  virtual task write_dcsr(rv_core_csr_dcsr_t dcsr);
    abstract_cmd_err_e status;
    abstract_cmd_reg_write(.regno(RvCoreCsrDcsr), .value_q({BUS_DW'(dcsr)}), .status(status));
    `DV_CHECK_EQ(status, AbstractCmdErrNone)
    step_entered = dcsr.step;
  endtask

  // Internal helper function which returns the address of a symbol from the elf file.
  protected virtual function logic [BUS_AW-1:0] get_symbol_address(string symbol);
    longint unsigned addr, size;
    // Return address if we already looked it up before.
    if (symbol_table.exists(symbol)) return symbol_table[symbol];
    `DV_CHECK(dv_utils_pkg::sw_symbol_get_addr_size(.elf_file(elf_file), .symbol(symbol),
                  .does_not_exist_ok(0), .addr(addr), .size(size)))
    return BUS_AW'(addr);
  endfunction

  // Internal helper function enforces either address or the symbol to be set.
  //
  // It throws an error if both, symbol and addr are set to known values. It also throws an error if
  // neither of them are set. If the symbol is set, then the address is updated to the symbol's
  // physical address.
  //
  // addr: The address. If set to 'x, it is updated to the symbol's physical address and returned.
  // symbol: The symbolic address.
  protected virtual function void addr_or_symbol_set(inout logic [BUS_AW-1:0] addr,
                                                     input string symbol);
    if (addr === 'x && symbol == "") begin
      `uvm_fatal(`gfn, "Either addr or symbol expected to be set. Neither are set.")
    end else if (addr !== 'x && symbol != "") begin
      `uvm_fatal(`gfn, "Either addr or symbol expected to be set. Both are set.")
    end
    if (symbol != "") addr = get_symbol_address(symbol);
  endfunction

  // Checks if the halted CPU's PC is at the given address or symbol.
  //
  // exp_addr: Expected address.
  // exp_symbol: Expected symbolic address.
  // error_if_eq: 0: throw error on mismatch, 1: throw error on match.
  // NOTE: Either exp_addr or exp_symbol must be set (pseudo-function overloading).
  virtual task check_pc(logic [BUS_AW-1:0] exp_addr = 'x,
                        string exp_symbol = "",
                        bit error_if_eq = 0);
    logic [BUS_DW-1:0] pc;
    addr_or_symbol_set(exp_addr, exp_symbol);
    read_pc(pc);
    if (error_if_eq)  `DV_CHECK_NE(pc, exp_addr)
    else              `DV_CHECK_EQ(pc, exp_addr)
  endtask

  // Checks if the reason for entering the debug mode matches the expected cause.
  //
  // exp_debug_cause: The expected debug cause.
  virtual task check_debug_cause(rv_core_csr_dcsr_cause_e exp_debug_cause);
    rv_core_csr_dcsr_t dcsr;
    read_dcsr(dcsr);
    `DV_CHECK_EQ(dcsr.cause, exp_debug_cause)
  endtask

  // Check if trigger select is valid.
  virtual task is_valid_tselect_index(input int index, output bit valid);
    abstract_cmd_err_e status;
    logic [BUS_DW-1:0] cmd_data[$];
    abstract_cmd_reg_write(.regno(RvCoreCsrTSelect), .value_q({index}), .status(status));
    `DV_CHECK_EQ(status, AbstractCmdErrNone)
    abstract_cmd_reg_read(.regno(RvCoreCsrTSelect), .value_q(cmd_data), .status(status));
    `DV_CHECK_EQ(status, AbstractCmdErrNone)
    valid = (index == cmd_data[0]);
  endtask

  // List breakpoints.
  //
  // TODO: Only match type breakpoints on address supported.
  // For each breakpoint, list the following information:
  // Breakpoint on addr|data 0x%0d before|after load|store|execute op.
  // breakpoints: The list of breakpoints returned to the caller.
  // delete_breakpoints: Optionally, enable deleting all breakpoints to allow further execution.
  virtual task info_breakpoints(output breakpoint_t breakpoints[$],
                                input bit delete_breakpoints = 0);
    abstract_cmd_err_e status;
    logic [BUS_DW-1:0] cmd_data[$];

    breakpoints.delete();
    for (int i = 0; i >= 0; i++) begin  // Infinite loop.
      bit valid;
      is_valid_tselect_index(i, valid);
      if (valid) begin
        rv_core_csr_trigger_mcontrol_t mcontrol;
        abstract_cmd_reg_read(.regno(RvCoreCsrTData1), .value_q(cmd_data), .status(status));
        `DV_CHECK_EQ(status, AbstractCmdErrNone)
        mcontrol = rv_core_csr_trigger_mcontrol_t'(cmd_data[0]);
        if (!(mcontrol.trigger_type == RvTriggerTypeMatch &&
              (mcontrol.load || mcontrol.store || mcontrol.execute))) continue;
        // This slot has as a valid breakpoint.
        abstract_cmd_reg_read(.regno(RvCoreCsrTData2), .value_q(cmd_data), .status(status));
        `DV_CHECK_EQ(status, AbstractCmdErrNone)
        breakpoints.push_back(
            '{trigger_type: RvTriggerTypeMatch,
              index       : i,
              tdata1      : BUS_DW'(mcontrol),
              tdata2      : cmd_data[0]});
        if (delete_breakpoints) clear_tdata1(0);
      end else break;
    end
    print_breakpoints(breakpoints);
  endtask

  // Prints breakpoints in human-friendly way.
  virtual function void print_breakpoints(ref breakpoint_t breakpoints[$]);
    string format = {"\n\t%0d: %0s type breakpoint on %0s 0x%0h %0s 3'b%0b(execute|store|load) ",
                     "op, with action %0s"};
    string msg = "";

    foreach (breakpoints[i]) begin
      rv_core_csr_trigger_mcontrol_t mcontrol = rv_core_csr_trigger_mcontrol_t'(
          breakpoints[i].tdata1);
      msg = {msg, $sformatf(format,
                            breakpoints[i].index,
                            breakpoints[i].trigger_type.name(),
                            mcontrol.select ? "data" : "addr",
                            breakpoints[i].tdata2,
                            mcontrol.timing ? "after" : "before",
                            {mcontrol.execute, mcontrol.store, mcontrol.load},
                            mcontrol.action.name())};
    end
    if (msg != "") `uvm_info(`gfn, msg, UVM_LOW)
    else           `uvm_info(`gfn, "No breakpoints added yet", UVM_LOW)
  endfunction

  // Insert a breakpoint at the given address or symbol.
  //
  // addr: The PC address.
  // symbol: Symbolic address.
  // TODO: Only trigger on exact address match before execution supported.
  virtual task add_breakpoint(logic [BUS_AW-1:0] addr = 'x, string symbol = "");
    abstract_cmd_err_e status;
    logic [BUS_DW-1:0] cmd_data[$];

    addr_or_symbol_set(addr, symbol);
    `uvm_info(`gfn, $sformatf("Adding breakpoint on 0x%0h(%0s)", addr, symbol), UVM_LOW)
    for (int i = 0; i >= 0; i++) begin  // Infinite loop.
      bit valid;
      is_valid_tselect_index(i, valid);
      if (valid) begin
        rv_core_csr_trigger_mcontrol_t mcontrol;
        abstract_cmd_reg_read(.regno(RvCoreCsrTData1), .value_q(cmd_data), .status(status));
        `DV_CHECK_EQ(status, AbstractCmdErrNone)
        mcontrol = rv_core_csr_trigger_mcontrol_t'(cmd_data[0]);
        if (mcontrol.trigger_type == RvTriggerTypeMatch &&
            (mcontrol.load || mcontrol.store || mcontrol.execute)) continue;
        // This slot is available for a new breakpoint.
        mcontrol.trigger_type = RvTriggerTypeMatch;
        mcontrol.dmode = 1;
        mcontrol.select = 0;
        mcontrol.timing = 0;
        mcontrol.action = RvTriggerActionEnterDebugMode;
        mcontrol.match = 0;
        mcontrol.u = 1;
        mcontrol.execute = 1;
        mcontrol.store = 0;
        mcontrol.load = 0;
        abstract_cmd_reg_write(.regno(RvCoreCsrTData1), .value_q({BUS_DW'(mcontrol)}),
                               .status(status));
        `DV_CHECK_EQ(status, AbstractCmdErrNone)
        abstract_cmd_reg_write(.regno(RvCoreCsrTData2), .value_q({addr}), .status(status));
        `DV_CHECK_EQ(status, AbstractCmdErrNone)
        return;
      end else break;
    end
    `uvm_error(`gfn, "No free breakpoint slots available")
  endtask

  // Restores previously deleted breakpoints.
  virtual task restore_breakpoints(breakpoint_t breakpoints[$]);
    `DV_CHECK(breakpoints.size())
    foreach (breakpoints[i]) begin
      abstract_cmd_err_e status;
      abstract_cmd_reg_write(.regno(RvCoreCsrTSelect), .value_q({breakpoints[i].index}),
                             .status(status));
      `DV_CHECK_EQ(status, AbstractCmdErrNone)
      abstract_cmd_reg_write(.regno(RvCoreCsrTData1), .value_q({breakpoints[i].tdata1}),
                             .status(status));
      `DV_CHECK_EQ(status, AbstractCmdErrNone)
      abstract_cmd_reg_write(.regno(RvCoreCsrTData2), .value_q({breakpoints[i].tdata2}),
                             .status(status));
      `DV_CHECK_EQ(status, AbstractCmdErrNone)
    end
  endtask

  // Clear trigger data1 register and optionally, tdata2 as well.
  //
  // clear_tdata2: Knob to clear tdata2 as well.
  // Note: It is upto the the caller to ensure the right trigger is selected first. Also, we are
  // leaving tdata2 in a stale state.
  protected virtual task clear_tdata1(bit clear_tdata2);
    abstract_cmd_err_e status;
    abstract_cmd_reg_write(.regno(RvCoreCsrTData1), .value_q({0}), .status(status));
    `DV_CHECK_EQ(status, AbstractCmdErrNone)
    if (clear_tdata2) begin
      abstract_cmd_reg_write(.regno(RvCoreCsrTData2), .value_q({0}), .status(status));
      `DV_CHECK_EQ(status, AbstractCmdErrNone)
    end
  endtask

  // Delete an existing breakpoint by index, or on the given address or symbol.
  //
  // index: The selected trigger index.
  // addr: The PC address.
  // symbol: Symbolic PC address.
  // clear_tdata2: Knob to clear tdata2 as well.
  // Note: Only either set index, addr or symbol.
  virtual task delete_breakpoint(logic [BUS_AW-1:0] addr = 'x,
                                 string symbol = "",
                                 int index = -1,
                                 bit clear_tdata2 = 0);
    abstract_cmd_err_e status;
    logic [BUS_DW-1:0] cmd_data[$];

    if (index != -1) begin
      bit valid;
      if (addr !== 'x || symbol != "") `uvm_fatal(`gfn, "Only set either index, or addr or symbol")
      is_valid_tselect_index(index, valid);

      if (valid) begin
        `uvm_info(`gfn, $sformatf("Deleting breakpoint at index %0d", index), UVM_LOW)
        clear_tdata1(clear_tdata2);
      end else begin
        `uvm_error(`gfn, $sformatf("Index %0d appears to be out of bounds", index))
      end
      return;
    end

    addr_or_symbol_set(addr, symbol);
    for (int i = 0; i >= 0; i++) begin  // Infinite loop.
      bit valid;
      is_valid_tselect_index(i, valid);
      if (valid) begin
        rv_core_csr_trigger_mcontrol_t mcontrol;
        abstract_cmd_reg_read(.regno(RvCoreCsrTData1), .value_q(cmd_data), .status(status));
        `DV_CHECK_EQ(status, AbstractCmdErrNone)
        mcontrol = rv_core_csr_trigger_mcontrol_t'(cmd_data[0]);
        if (!(mcontrol.trigger_type == RvTriggerTypeMatch &&
              (mcontrol.load || mcontrol.store || mcontrol.execute))) continue;
        // This slot has as a valid breakpoint. Check if address matches.
        abstract_cmd_reg_read(.regno(RvCoreCsrTData2), .value_q(cmd_data), .status(status));
        `DV_CHECK_EQ(status, AbstractCmdErrNone)
        if (addr == cmd_data[0]) begin
          `uvm_info(`gfn, $sformatf("Deleting breakpoint on 0x%0h(%0s)", addr, symbol), UVM_LOW)
          clear_tdata1(clear_tdata2);
          return;
        end
      end else break;
    end
    `uvm_error(`gfn, $sformatf("No breakpoint found associated with addr 0x%0h (%s)", addr,
                               symbol))
  endtask

  // Single step.
  //
  // Read-modify-writes the DCSR register with the step field set to 1. The `step_entered` local
  // status bit is checked for improved performance.
  virtual task step(int num = 1);
    if (!step_entered) begin
      rv_core_csr_dcsr_t dcsr;
      read_dcsr(dcsr);
      dcsr.step = 1;
      write_dcsr(dcsr);
    end
    `uvm_info(`gfn, "Single stepping", UVM_LOW)
    set_resumereq(1);
    wait_cpu_halted();
  endtask

  // Resume execution after entering a halted state.
  //
  // Equivalent of `continue` gdb command (`continue` is a reserved keyword in SystemVerilog, so we
  // pick the name `continue_execution()` instead).
  // If there is a breakpoint on the DPC register, then this task deletes all breakpoints,
  // single-steps, restores all breakpoints and then resumes.
  // do_wait_cpu_resumed: Optionally, poll the dmstatus register to wait for the CPU to have
  //                      resumed (default off).
  virtual task continue_execution(bit do_wait_cpu_resumed = 0);
    logic [BUS_DW-1:0] pc;
    breakpoint_t breakpoints[$];
    rv_core_csr_dcsr_t dcsr;

    read_pc(pc);
    info_breakpoints(.breakpoints(breakpoints));
    foreach (breakpoints[i]) begin
      if (breakpoints[i].tdata2 == pc) begin
        delete_breakpoint(.addr(pc));
        step();
        restore_breakpoints(.breakpoints({breakpoints[i]}));
        break;
      end
    end

    read_dcsr(dcsr);
    dcsr.step = 0;
    write_dcsr(dcsr);
    `uvm_info(`gfn, "Continuing execution", UVM_LOW)
    set_resumereq(1);

    // NOTE: It may take a short while for the CPU to resume. If there are other upcoming
    // breakpoints, the CPU may execute and immediately halt again, by the time `wait_cpu_resumed()`
    // reads the dmstatus register to ascertain the CPU has indeed resumed. That will result in a
    // timeout error. So, it is left to the caller to synchronize these events. The step below is
    // hence conditioned on an optional argument which is set to 0 by default.
    if (do_wait_cpu_resumed) wait_cpu_resumed();
  endtask

  // Execute calls as one instruction.
  virtual task next();
    `uvm_fatal(`gfn, "Not implemented")
  endtask

  // Finish executing the current function.
  //
  // It is assumed that the CPU is in a halted state at this point, and has just begun executing an
  // arbitrary function. It reads the CPU's RA register and adds a breakpoint on it before
  // continuing the execution.
  //
  // Note that this task adds a new breakpoint on the return address. After the CPU resumes, it
  // waits for a few TCK cycles to let the CPU exit the debug mode. Then, it waits for the CPU to
  // halt again. When it halts, the newly added breakpoint is deleted.
  // return_address: Use an externally provided return address. If set to X, it reads the return
  //                 address from the RA register.
  // noreturn_function: Indicate that the function does not return. If set to 1, a breakpoint on RA
  //                    is not added, and the task exits immediately after having the CPU continue
  //                    executing the function.
  virtual task finish(logic [BUS_AW-1:0] return_address = 'x, bit noreturn_function = 0);
    if (return_address === 'x) begin
      abstract_cmd_err_e status;
      logic [BUS_DW-1:0] cmd_data[$];
      abstract_cmd_reg_read(.regno(RvCoreCsrGprRa), .value_q(cmd_data), .status(status));
      `DV_CHECK_EQ(status, AbstractCmdErrNone)
      return_address = BUS_AW'(cmd_data[0]);
    end
    `uvm_info(`gfn, $sformatf("Adding a breakpoint on the return address: 0x%0h",
                              return_address), UVM_MEDIUM)

    if (!noreturn_function) add_breakpoint(.addr(return_address));
    continue_execution();
    if (!noreturn_function) begin
      // It is better to wait for a few TCKs than call wait_cpu_resumed(), since the latter takes a
      // long time, within which the CPU could have re-entered the halted state.
      cfg.vif.wait_tck(20);
      wait_cpu_halted();
      check_pc(.exp_addr(return_address));
      delete_breakpoint(.addr(return_address));
    end
  endtask

  // Have the CPU execute a function with the specified arguments.
  //
  // addr: The function address.
  // symbol: The function's symbol.
  // args: The function args.
  // noreturn_function: Indicate that the CPU does not return from this function.
  virtual task call(logic [BUS_AW-1:0] addr = 'x,
                    string symbol = "",
                    logic [BUS_DW-1:0] args[$] = {},
                    bit noreturn_function = 0);
    byte status;
    abstract_cmd_err_e abs_status;
    logic [BUS_DW-1:0] cmd_data[$];
    logic [BUS_DW-1:0] gprs[abstract_cmd_regno_t], new_sp;

    `uvm_info(`gfn, "Saving all necessary GPRS", UVM_MEDIUM)
    `DV_CHECK(args.size() <= 8)
    abstract_cmd_reg_read(.regno(RvCoreCsrGprRa), .value_q(cmd_data), .status(abs_status));
    `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
    gprs[RvCoreCsrGprRa] = cmd_data[0];
    abstract_cmd_reg_read(.regno(RvCoreCsrGprSp), .value_q(cmd_data), .status(abs_status));
    `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
    gprs[RvCoreCsrGprSp] = cmd_data[0];
    // Setup a new stack 32 bytes from the current stack pointer, and align it to 32 bytes.
    new_sp = (cmd_data[0] - 32) & ~('h1f);
    abstract_cmd_reg_read(.regno(RvCoreCsrGprGp), .value_q(cmd_data), .status(abs_status));
    `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
    gprs[RvCoreCsrGprGp] = cmd_data[0];
    for (int i = 0; i < cmd_data.size(); i++) begin
      abstract_cmd_reg_read(.regno(RvCoreCsrGprA0 + i), .value_q(cmd_data), .status(abs_status));
      `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
      gprs[RvCoreCsrGprA0 + i] = cmd_data[0];
    end
    read_pc(gprs[RvCoreCsrDpc]);

    `uvm_info(`gfn, $sformatf("Setting new SP and RA: 0x%0h", new_sp), UVM_MEDIUM)
    abstract_cmd_reg_write(.regno(RvCoreCsrGprRa), .value_q({new_sp}), .status(abs_status));
    `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
    abstract_cmd_reg_write(.regno(RvCoreCsrGprSp), .value_q({new_sp}), .status(abs_status));
    `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
    `uvm_info(`gfn, "Writing the opcode 'ebreak' at the SP address", UVM_MEDIUM)
    mem_write(.addr(new_sp), .value_q({Ebreak}), .status(status));
    `DV_CHECK_EQ(status, 0)
    `uvm_info(`gfn, $sformatf("Writing function arguments [%p] to A registers", args), UVM_MEDIUM)
    foreach (args[i]) begin
      abstract_cmd_reg_write(.regno(RvCoreCsrGprA0 + i), .value_q({args[i]}), .status(abs_status));
      `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
    end

    write_pc(addr, symbol);
    finish(.return_address(new_sp), .noreturn_function(noreturn_function));

    if (!noreturn_function) begin
      foreach (gprs[i]) begin
        abstract_cmd_reg_write(.regno(i), .value_q({gprs[i]}), .status(abs_status));
        `DV_CHECK_EQ(abs_status, AbstractCmdErrNone)
      end
      `uvm_info(`gfn, "Restored all necessary GPRS", UVM_MEDIUM)
    end
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
                        output logic [BUS_DW-1:0] value_q[$],
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
    value_q = sba_item.rdata;
    status = sba_item.is_err;
    `DV_CHECK(!sba_item.is_busy_err)
    `DV_CHECK(!sba_item.timed_out)
  endtask

  // Simplified version of sba_access(), for 32-bit writes.
  virtual task sba_write(input logic [BUS_AW-1:0] addr,
                         input logic [BUS_DW-1:0] value_q[$],
                         output sba_access_err_e status);
    sba_access_item sba_item = sba_access_item::type_id::create("sba_item");
    sba_item.bus_op = BusOpWrite;
    sba_item.addr = addr;
    sba_item.wdata = value_q;
    sba_item.size = SbaAccessSize32b;
    sba_item.autoincrement = value_q.size() > 1 ? value_q.size() : 0;
    sba_access(sba_item);
    status = sba_item.is_err;
    `DV_CHECK(!sba_item.is_busy_err)
    `DV_CHECK(!sba_item.timed_out)
  endtask

  // Wrapper task for reading the system memory either via SBA or via program buffer.
  //
  // addr: The starting system address.
  // value_q: The read data returned to the caller.
  // status: The status of the op returned to the caller.
  // size: The size of the read access in terms of full bus words.
  // route: The route taken to access the system memory.
  virtual task mem_read(input logic [BUS_AW-1:0] addr,
                        output logic [BUS_DW-1:0] value_q[$],
                        output byte status,
                        input mem_access_route_e route = randomize_mem_access_route(),
                        input int size = 1);
    case (route)
      MemAccessViaAbstractCmd, MemAccessViaProgbuf: begin
        abstract_cmd_err_e abs_status;
        abstract_cmd_mem_read(.addr(addr), .value_q(value_q), .status(abs_status), .size(size),
                              .route(route));
        status = byte'(abs_status);
      end
      MemAccessViaSba: begin
        sba_access_err_e sba_status;
        sba_read(.addr(addr), .value_q(value_q), .status(sba_status), .size(size));
        status = byte'(sba_status);
      end
      default: `uvm_fatal(`gfn, $sformatf("Invalid route: 0x%0h", route))
    endcase
  endtask

  // Wrapper task for writing to the system memory either via SBA or via program buffer.
  //
  // addr: The starting address of the system memory.
  // value_q: The read data returned to the caller.
  // status: The status of the op returned to the caller.
  // size: The size of the read access in terms of full bus words.
  // route: The route taken to access the system memory.
  virtual task mem_write(input logic [BUS_AW-1:0] addr,
                         input logic [BUS_DW-1:0] value_q[$],
                         output byte status,
                         input mem_access_route_e route = randomize_mem_access_route());
    case (route)
      MemAccessViaAbstractCmd, MemAccessViaProgbuf: begin
        abstract_cmd_err_e abs_status;
        abstract_cmd_mem_write(.addr(addr), .value_q(value_q), .status(abs_status), .route(route));
        status = byte'(abs_status);
      end
      MemAccessViaSba: begin
        sba_access_err_e sba_status;
        sba_write(.addr(addr), .value_q(value_q), .status(sba_status));
        status = byte'(sba_status);
      end
      default: `uvm_fatal(`gfn, $sformatf("Invalid route: 0x%0h", route))
    endcase
  endtask

  // Load a memory location in the device with a custom image.
  //
  // Reads a VMEM file and writes the contents to the memory.
  // vmem_file: Path to vmem file. Must be BUS_DW word sized.
  // addr: The starting address of the system memory.
  // route: The route taken to access the system memory.
  virtual task load_image(string vmem_file,
                          logic [BUS_AW-1:0] addr,
                          input mem_access_route_e route = randomize_mem_access_route());
    logic [BUS_DW-1:0] vmem_data[$];
    byte status;
    dv_utils_pkg::read_vmem(vmem_file, vmem_data);
    `DV_CHECK_FATAL(vmem_data.size(), "vmem_data is empty!")
    mem_write(.addr(addr), .value_q(vmem_data), .status(status), .route(route));
    `DV_CHECK_EQ(status, 0)
  endtask

  virtual function mem_access_route_e randomize_mem_access_route();
    mem_access_route_e route;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(route,
                                       route inside {MemAccessViaProgbuf, MemAccessViaSba};)
    return route;
  endfunction

endclass
