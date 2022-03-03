// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A package that provides common SBA access utilities from JTAG.
package sba_access_utils_pkg;
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import bus_params_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import jtag_agent_pkg::*;
  import jtag_dmi_agent_pkg::*;
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef enum logic [2:0] {
    SbaAccessSize8b,
    SbaAccessSize16b,
    SbaAccessSize32b,
    SbaAccessSize64b,
    SbaAccessSize128b
  } sba_access_size_e;

  typedef enum logic [2:0] {
    SbaErrNone = 0,
    SbaErrTimeout = 1,
    SbaErrBadAddr = 2,
    SbaErrBadAlignment = 3,
    SbaErrBadSize = 4,
    SbaErrOther = 7
  } sba_access_err_e;

  localparam string MsgId = "sba_access_utils";

  // Initiates a single SBA access through JTAG (-> DTM -> DMI -> SBA).
  //
  // It writes DMI SBA registers to create a read or write access on the system bus, poll for its
  // completion and return the response (on reads).
  // jtag_dmi_ral: A handle to the DMI RAL block that has the SBA registers.
  // cfg: A handle to the jtag_agent_cfg.
  // bus_op: read or a write request.
  // size: transfer size in bytes (0: 1 byte, 1: 2 bytes ...).
  // addr: External system address.
  // data: data written or read. TODO: Needs to be a queue if autoincrement is set.
  // readonaddr: Trigger SBA read automatically on writing address.
  // readondata: Trigger SBA read automatically on reading data.
  // autoincrement: Automatically increment address by size bytes and trigger new access. TODO: TBD
  task automatic sba_access(input jtag_dmi_reg_block jtag_dmi_ral,
                            input jtag_agent_cfg cfg,
                            input bus_op_e bus_op,
                            input sba_access_size_e size,
                            input logic [BUS_AW-1:0] addr,
                            inout logic [BUS_DW-1:0] data,
                            input logic readonaddr = 1'b1,
                            input logic readondata = 1'b0,
                            input logic autoincrement = 1'b0);

    uvm_reg_data_t rdata, wdata;
    logic is_busy, is_busy_err;
    sba_access_err_e is_err;

    // Update sbcs for the new transaction.
    wdata = jtag_dmi_ral.sbcs.get_mirrored_value();
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbaccess, wdata, size);
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadonaddr, wdata, readonaddr);
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadondata, wdata, readondata);
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbautoincrement, wdata, autoincrement);
    if (wdata != jtag_dmi_ral.sbcs.sbaccess.get_mirrored_value()) begin
      csr_wr(.ptr(jtag_dmi_ral.sbcs), .value(wdata));
    end

    // Initiate the request.
    csr_wr(.ptr(jtag_dmi_ral.sbaddress0), .value(addr));
    if (bus_op == BusOpRead) begin
      if (readonaddr) begin
        // Do nothing.
      end else if (readondata) begin
        // Read the data to trigger the read accesss.
        csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rdata));
      end else begin
        `uvm_info(MsgId, {"readonaddr and readondata are not set. ",
                          "Read request will not be triggered. Returning."}, UVM_MEDIUM)
        return;
      end
    end else begin
      csr_wr(.ptr(jtag_dmi_ral.sbdata0), .value(data));
    end

    // Wait for access to complete.
    sba_access_busy_wait(jtag_dmi_ral, cfg, is_busy, is_busy_err, is_err);

    // Return the data on reads.
    if (!is_busy && !is_busy_err && !is_err && bus_op == BusOpRead && !cfg.in_reset) begin
      csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(data));
    end
  endtask

  // Read the SBA access status.
  task automatic sba_access_status(input jtag_dmi_reg_block jtag_dmi_ral,
                                   output logic is_busy,
                                   output logic is_busy_err,
                                   output sba_access_err_e is_err);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dmi_ral.sbcs), .value(rdata));
    is_busy = get_field_val(jtag_dmi_ral.sbcs.sbbusy, rdata);
    is_busy_err = get_field_val(jtag_dmi_ral.sbcs.sbbusyerror, rdata);
    is_err = sba_access_err_e'(get_field_val(jtag_dmi_ral.sbcs.sberror, rdata));
    `uvm_info(MsgId, $sformatf("SBA req status: is_busy: %0b, is_busy_err: %0b, is_err: %0s",
                               is_busy, is_busy_err, is_err.name()), UVM_HIGH)
  endtask

  // Reads sbcs register to poll and wait for access to complete.
  task automatic sba_access_busy_wait(input jtag_dmi_reg_block jtag_dmi_ral,
                                      input jtag_agent_cfg cfg,
                                      output logic is_busy,
                                      output logic is_busy_err,
                                      output sba_access_err_e is_err);
    `DV_SPINWAIT_EXIT(
      do begin
        sba_access_status(jtag_dmi_ral, is_busy, is_busy_err, is_err);
        `DV_CHECK_EQ(is_busy_err, 0, "sbbusyerror is not expected to be set", , MsgId)
        // TODO: Make this optional.
        sba_access_error_clear(jtag_dmi_ral, is_busy_err, is_err);
        if (is_err != SbaErrNone) `DV_CHECK_EQ(is_busy, 0, , , MsgId)
      end while (is_busy);,
      begin
        fork
          // TODO: Provide callbacks to support waiting for custom exit events.
          wait(cfg.in_reset);
          // TODO: Make this timeout more configurable.
          dv_utils_pkg::wait_timeout(cfg.vif.tck_period_ns * 10000);
        join_any
      end,
      , MsgId
    )
  endtask

  // Clear SBA access busy error and access error sticky bits if they are set.
  task automatic sba_access_error_clear(jtag_dmi_reg_block jtag_dmi_ral,
                                        logic is_busy_err,
                                        sba_access_err_e is_err);
    uvm_reg_data_t data;
    if (!is_busy_err && is_err == SbaErrNone) return;
    `uvm_info(MsgId, $sformatf("Clearing SBA access errors: is_busy_err: %0b, is_err: %0s",
                               is_busy_err, is_err.name()), UVM_MEDIUM)

    data = jtag_dmi_ral.sbcs.get_mirrored_value();
    if (is_busy_err) begin
      data = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbbusyerror, data, 1);
    end
    if (is_err != SbaErrNone) begin
      data = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sberror, data, 1);
    end
    csr_wr(.ptr(jtag_dmi_ral.sbcs), .value(data));
  endtask

endpackage
