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
  import dv_lib_pkg::*;
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
  //
  // jtag_dmi_ral: A handle to the DMI RAL block that has the SBA registers.
  // cfg: A handle to the jtag_agent_cfg.
  // req: The SBA access request item. It will be updated with the responses.
  // sba_access_err_clear: Knob to clear the SBA access errors.
  task automatic sba_access(input jtag_dmi_reg_block jtag_dmi_ral,
                            input jtag_agent_cfg cfg,
                            input sba_access_item req,
                            input bit sba_access_err_clear = 1'b1);

    uvm_reg_data_t rdata, wdata;

    // Update sbcs for the new transaction.
    wdata = jtag_dmi_ral.sbcs.get_mirrored_value();
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbaccess, wdata, req.size);
    if (req.bus_op == BusOpRead) begin
      wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadonaddr, wdata, req.readonaddr);
      wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadondata, wdata, req.readondata);
    end else begin
      // If we set these bits on writes, it complicates things.
      wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadonaddr, wdata, 0);
      wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadondata, wdata, 0);
    end
    wdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbautoincrement, wdata,
                                           (req.autoincrement > 0));
    if (wdata != jtag_dmi_ral.sbcs.sbaccess.get_mirrored_value()) begin
      csr_wr(.ptr(jtag_dmi_ral.sbcs), .value(wdata), .predict(1));
    end

    // Update the sbaddress0.
    csr_wr(.ptr(jtag_dmi_ral.sbaddress0), .value(req.addr), .predict(1));

    // These steps are run in several branches in the following code. Macroize them.
`define BUSYWAIT_AND_EXIT_ON_ERR                                                          \
  sba_access_busy_wait_and_clear_error(.jtag_dmi_ral(jtag_dmi_ral), .cfg(cfg), .req(req), \
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
          `uvm_info(MsgId, {"readonaddr and readondata are not set. ",
                            "Read request will not be triggered. Returning."}, UVM_MEDIUM)
        end
        2'b01: begin
          // SBA read already triggered on write to sbaddress0. Read sbdata0 to fetch the response
          // data. If autoincrement is set, then return to the caller - it is not a valid usecase.
          `BUSYWAIT_AND_EXIT_ON_ERR
          if (!cfg.in_reset) begin
            csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rdata));
            req.rdata[0] = rdata;
          end
        end
        2'b10, 2'b11: begin
          if (!req.readonaddr) begin
            // The first read to sbdata returns stale data. Discard it.
            if (!cfg.in_reset) begin
              csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rdata));
            end
          end
          // The previous step triggered an SBA read. Wait for it to complete.
          `BUSYWAIT_AND_EXIT_ON_ERR

          // Read sbdata req.autoincrement+1 number of times.
          //
          // Randomly also inject reads to sbaddress0 to verify address is correctly incremented
          // (done externally by the scoreboard).
          for (int i = 0; i < req.autoincrement + 1; i++) begin
            if (!cfg.in_reset) begin
              csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rdata));
              req.rdata[i] = rdata;
            end
            `BUSYWAIT_AND_EXIT_ON_ERR
            if (i > 0 && !cfg.in_reset && !$urandom_range(0, 3)) begin  //25%
              csr_rd(.ptr(jtag_dmi_ral.sbaddress0), .value(rdata));
            end
          end
        end
        default: begin
          `uvm_fatal(MsgId, "Unreachable!")
        end
      endcase
    end else begin
      // Write sbdata req.autoincrement+1 number of times.
      //
      // Randomly also inject reads to sbaddress0 to verify address is correctly incremented
      // (done externally by the scoreboard).
      for (int i = 0; i < req.autoincrement + 1; i++) begin
        if (!cfg.in_reset) begin
          csr_wr(.ptr(jtag_dmi_ral.sbdata0), .value(req.wdata[i]), .predict(1));
        end
        `BUSYWAIT_AND_EXIT_ON_ERR
        if (i > 0 && !cfg.in_reset && !$urandom_range(0, 3)) begin  //25%
          csr_rd(.ptr(jtag_dmi_ral.sbaddress0), .value(rdata));
        end
      end
    end

`undef BUSYWAIT_AND_EXIT_ON_ERR
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
    if (!is_busy) begin
      `uvm_info(MsgId, $sformatf("SBA req completed: %0s", req.sprint(uvm_default_line_printer)),
                UVM_HIGH)
    end
  endtask

  // Reads sbcs register to poll and wait for access to complete.
  task automatic sba_access_busy_wait(input jtag_dmi_reg_block jtag_dmi_ral,
                                      input jtag_agent_cfg cfg,
                                      input sba_access_item req);
    logic is_busy;
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
  task automatic sba_access_error_clear(jtag_dmi_reg_block jtag_dmi_ral, sba_access_item req,
                                        bit clear_sbbusyerror = 1'b1, bit clear_sberror = 1'b1);
    uvm_reg_data_t data = jtag_dmi_ral.sbcs.get_mirrored_value();
    if (clear_sbbusyerror && req.is_busy_err) begin
      data = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbbusyerror, data, 1);
    end
    if (clear_sberror && req.is_err != SbaErrNone) begin
      data = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sberror, data, 1);
    end
    csr_wr(.ptr(jtag_dmi_ral.sbcs), .value(data), .predict(1));
  endtask

  // Wrapper task for busy wait followed by clearing of sberror if an error was reported.
  task automatic sba_access_busy_wait_and_clear_error(input jtag_dmi_reg_block jtag_dmi_ral,
                                                      input jtag_agent_cfg cfg,
                                                      input sba_access_item req,
                                                      input bit sba_access_err_clear);
    sba_access_busy_wait(jtag_dmi_ral, cfg, req);
    // Only clear sberror - let the caller handle sbbusyerror.
    if (!cfg.in_reset && sba_access_err_clear && req.is_err != SbaErrNone) begin
      sba_access_error_clear(.jtag_dmi_ral(jtag_dmi_ral), .req(req), .clear_sbbusyerror(0));
    end
  endtask


  `include "sba_access_item.sv"
  `include "sba_access_monitor.sv"

endpackage
