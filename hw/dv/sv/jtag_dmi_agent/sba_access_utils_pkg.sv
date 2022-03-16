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
  typedef class sba_access_item;

  // Initiates a single SBA access through JTAG (-> DTM -> DMI -> SBA).
  //
  // It writes DMI SBA registers to create a read or write access on the system bus, poll for its
  // completion and return the response (on reads).
  // jtag_dmi_ral: A handle to the DMI RAL block that has the SBA registers.
  // cfg: A handle to the jtag_agent_cfg.
  // req: The SBA access request item. It will be updated with the responses.
  // sba_access_err_clear: Knob to clear the SBA access errors.
  task automatic sba_access(input jtag_dmi_reg_block jtag_dmi_ral,
                            input jtag_agent_cfg cfg,
                            input sba_access_item req,
                            input bit sba_access_err_clear = 1'b1);

    uvm_reg_data_t rdata, wdata;
    logic is_busy;

    // Update sbcs for the new transaction.
    wdata = jtag_dmi_ral.sbcs.get_mirrored_value();
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbaccess, wdata, req.size);
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadonaddr, wdata, req.readonaddr);
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadondata, wdata, req.readondata);
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbautoincrement, wdata,
                                           req.autoincrement);
    if (wdata != jtag_dmi_ral.sbcs.sbaccess.get_mirrored_value()) begin
      csr_wr(.ptr(jtag_dmi_ral.sbcs), .value(wdata));
    end

    // Initiate the request.
    // Writing to addr with readonaddr set will trigger an SBA read.
    csr_wr(.ptr(jtag_dmi_ral.sbaddress0), .value(req.addr));
    if (req.bus_op == BusOpRead) begin
      if (!req.readonaddr && req.readondata) begin
        // Read the data to trigger the read accesss, only if readonaddr was not set.
        csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rdata));
      end
      if (!req.readonaddr && !req.readondata) begin
        `uvm_info(MsgId, {"readonaddr and readondata are not set. ",
                          "Read request will not be triggered. Returning."}, UVM_MEDIUM)
        return;
      end
    end else begin
      csr_wr(.ptr(jtag_dmi_ral.sbdata0), .value(req.wdata));
    end

    // Wait for the access to complete.
    sba_access_busy_wait(jtag_dmi_ral, cfg, req, is_busy);

    // If the access returns with an error, then the request was not made - return back to the
    // caller.
    if (req.is_busy_err || req.is_err != SbaErrNone) begin
      if (!cfg.in_reset && sba_access_err_clear) begin
        sba_access_error_clear(jtag_dmi_ral, req);
      end
      return;
    end

    // Return the data on reads.
    if (req.bus_op == BusOpRead && !cfg.in_reset && !is_busy) begin
      csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(req.rdata));
    end
  endtask

  // Read the SBA access status.
  task automatic sba_access_status(input jtag_dmi_reg_block jtag_dmi_ral,
                                   input sba_access_item req,
                                   output logic is_busy);
    uvm_reg_data_t data;
    csr_rd(.ptr(jtag_dmi_ral.sbcs), .value(data));
    is_busy = get_field_val(jtag_dmi_ral.sbcs.sbbusy, data);
    req.is_busy_err = get_field_val(jtag_dmi_ral.sbcs.sbbusyerror, data);
    req.is_err = sba_access_err_e'(get_field_val(jtag_dmi_ral.sbcs.sberror, data));
    `uvm_info(MsgId, $sformatf("SBA req status: %0s", req.sprint(uvm_default_line_printer)),
              UVM_HIGH)
  endtask

  // Reads sbcs register to poll and wait for access to complete.
  task automatic sba_access_busy_wait(input jtag_dmi_reg_block jtag_dmi_ral,
                                      input jtag_agent_cfg cfg,
                                      input sba_access_item req,
                                      output logic is_busy);
    `DV_SPINWAIT_EXIT(
      do begin
        sba_access_status(jtag_dmi_ral, req, is_busy);
        if (req.is_err != SbaErrNone) `DV_CHECK_EQ(is_busy, 0, , , MsgId)
      end while (is_busy && !req.is_busy_err);,
      begin
        fork
          // TODO: Provide callbacks to support waiting for custom exit events.
          wait(cfg.in_reset);
          begin
            // TODO: Make this timeout controllable.
            #(cfg.vif.tck_period_ns * 100000 * 1ns);
            req.timed_out = 1'b1;
            `uvm_info(MsgId, $sformatf("SBA req timed out: %0s",
                                       req.sprint(uvm_default_line_printer)), UVM_LOW)
          end
        join_any
      end,
      , MsgId
    )
  endtask

  // Clear SBA access busy error and access error sticky bits if they are set.
  //
  // Note that the req argument will continue to reflect the error bits.
  task automatic sba_access_error_clear(jtag_dmi_reg_block jtag_dmi_ral, sba_access_item req);
    uvm_reg_data_t data = jtag_dmi_ral.sbcs.get_mirrored_value();
    if (req.is_busy_err) begin
      data = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbbusyerror, data, 1);
    end
    if (req.is_err != SbaErrNone) begin
      data = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sberror, data, 1);
    end
    csr_wr(.ptr(jtag_dmi_ral.sbcs), .value(data));
  endtask

  `include "sba_access_item.sv"

endpackage
