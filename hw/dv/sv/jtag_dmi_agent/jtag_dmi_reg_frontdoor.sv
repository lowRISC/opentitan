// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Frontdoor (indirect) access of JTAG DMI registers for use within the RAL.
//
// JTAG DMI registers are accessed indirectly by writing {op, addr, data} to the JTAG DTM DMI
// register and polling it back for status and the response.
class jtag_dmi_reg_frontdoor extends uvm_reg_frontdoor;
  `uvm_object_utils(jtag_dmi_reg_frontdoor)

  // Handle to JTAG agent cfg which has the handle to the DTM RAL model and the vif.
  jtag_agent_cfg jtag_agent_cfg_h;

  // The same frontdoor instance can be attached to all DMI registers, since they all need to be
  // accessed via the same shared resource (the DTM DMI register). The semaphore ensures atomicity.
  // This is created and set externally, because it needs to be singular for all instances of this
  // object.
  semaphore jtag_dtm_ral_sem_h;

  `uvm_object_new

  virtual task body();
    csr_field_t         csr_or_fld;
    uvm_reg_data_t      wdata = 0;
    jtag_dtm_reg_block  jtag_dtm_ral = jtag_agent_cfg_h.jtag_dtm_ral;

    // Configure the JTAG agent to have a positive run-to-clear length, ensuring that DMI operations
    // make it from dmi_jtag to dm_top and back again before TCK stops.
    jtag_agent_cfg_h.rtc_length = 4;

    // If the JTAG agent is sitting in reset, print a debug message and exit early
    if (jtag_agent_cfg_h.in_reset) begin
      `uvm_info(`gfn, "DMI CSR req skipped due to reset", UVM_HIGH)
      return;
    end

    jtag_dtm_ral_sem_h.get();
    `uvm_info(`gfn, $sformatf("DMI CSR req started: %0s", rw_info.convert2string()), UVM_HIGH)

    `DV_CHECK_FATAL(rw_info.element_kind inside {UVM_REG, UVM_FIELD})
    `DV_CHECK_FATAL(rw_info.kind inside {UVM_READ, UVM_WRITE})
    `DV_CHECK_FATAL(rw_info.path == UVM_FRONTDOOR)
    csr_or_fld = decode_csr_or_field(rw_info.element);

    // Prepare the transaction by setting wdata as concatenated value of {addr, data, op} obtained
    // from this transaction.
    if (rw_info.kind == UVM_WRITE) begin
      // Extract an intended register value from rw_info.value[0]. If we're updating a field, we'll
      // put things in the right place next.
      wdata = rw_info.value[0];

      // If we were actually only updating a field, we'll have to do a pretend read-modify-write,
      // using the CSR's mirrored value.
      if (csr_or_fld.field != null) begin
        wdata = get_csr_val_with_updated_field(csr_or_fld.field,
                                               csr_or_fld.csr.get_mirrored_value(),
                                               rw_info.value[0]);
      end
    end

    // At this point, wdata is zero if this is a UVM_READ and is the write value for the CSR if this
    // is a UVM_WRITE. Shift the bits as necessary so that they are laid out in the right place for
    // the data field inside the DMI register.
    wdata = get_csr_val_with_updated_field(jtag_dtm_ral.dmi.data, '0, wdata);

    // Add in the op and address fields. When this is done, wdata is suitable for writing over JTAG
    // in order to perform the requested DMI operation (read or write).
    wdata = get_csr_val_with_updated_field(jtag_dtm_ral.dmi.op, wdata,
                                           (rw_info.kind == UVM_WRITE ? DmiOpWrite : DmiOpRead));
    wdata = get_csr_val_with_updated_field(jtag_dtm_ral.dmi.address, wdata,
                                           csr_or_fld.csr.get_address());

    // Start the DMI request.
    csr_wr(.ptr(jtag_dtm_ral.dmi), .value(wdata), .blocking(1), .predict(1));

    if (jtag_agent_cfg_h.in_reset) begin
      `uvm_info(`gfn, "DMI operation aborted: reset happened in middle of request", UVM_HIGH)
      jtag_dtm_ral_sem_h.put();
      return;
    end

    // Wait 10 tck cycles to allow the DMI req to complete. If we read the DTM DMI register too
    // soon, it may end up setting the in progress sticky bit, causing more time wasted. If there is
    // a reset in the middle of the wait, stop immediately.
    fork begin
      fork
        jtag_agent_cfg_h.vif.wait_tck(10);
        wait(jtag_agent_cfg_h.in_reset);
      join_any
      disable fork;
    end join
    if (jtag_agent_cfg_h.in_reset) begin
      `uvm_info(`gfn, "DMI operation aborted: reset happened in middle of request", UVM_HIGH)
      jtag_dtm_ral_sem_h.put();
      return;
    end

    // Do repeated reads of the DMI register to poll for completion, stopping early if we see a
    // reset. Run this in parallel with a 10k TCK cycle wait so that we'll fail reasonably quickly
    // if something gets completely stuck.
    fork begin : isolation_fork
      bit saw_completion = 1'b0;

      fork
        begin
          poll_for_completion(jtag_dtm_ral, csr_or_fld.field);
          saw_completion = 1'b1;
        end
        jtag_agent_cfg_h.vif.wait_tck(10_000);
      join_any

      // The DMI operation should have completed in the time we were waiting
      `DV_CHECK(saw_completion)

      disable fork;
    end join

    `uvm_info(`gfn, $sformatf("DMI CSR req completed: %0s", rw_info.convert2string()), UVM_HIGH)
    jtag_dtm_ral_sem_h.put();
  endtask

  // Poll the DMI register over JTAG and wait until the operation is no longer in progress.
  //
  // When the operation completes, details are written to rw_info. If this is a read of a field
  // (rather than an entire register), that should be passed as the field argument and this is used
  // when constructing rdata.
  //
  // If there is a reset while we are waiting for completion, stop and set rw_info.status to
  // UVM_NOT_OK.
  task poll_for_completion(jtag_dtm_reg_block jtag_dtm_ral, uvm_reg_field field);
    forever begin
      uvm_reg_data_t    rdata;
      jtag_dmi_op_rsp_e op_rsp;

      // Try to read the DMI register over JTAG
      csr_rd(.ptr(jtag_dtm_ral.dmi), .value(rdata), .blocking(1));

      // If there was a JTAG reset in the meantime, set rw_info.status to UVM_NOT_OK and return.
      if (jtag_agent_cfg_h.in_reset) begin
        rw_info.status = UVM_NOT_OK;
        return;
      end

      op_rsp = jtag_dmi_op_rsp_e'(get_field_val(jtag_dtm_ral.dmi.op, rdata));
      `uvm_info(`gfn, $sformatf("DMI CSR req status: %0s", op_rsp.name()), UVM_HIGH)

      // If op_rsp isn't DmiOpInProgress then the DMI operation has run to completion. Write the
      // details of the response into rw_info and then return.
      if (op_rsp != DmiOpInProgress) begin
        rw_info.status = op_rsp == DmiOpOk ? UVM_IS_OK : UVM_NOT_OK;
        if (rw_info.kind == UVM_READ) begin
          rdata = get_field_val(jtag_dtm_ral.dmi.data, rdata);
          if (field != null) begin
            rdata = get_field_val(field, rdata);
          end
          rw_info.value = new[1];
          rw_info.value[0] = rdata;
        end
        return;
      end

      // Otherwise, the operation was still in progress. Clear the (sticky) flag.
      csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmireset), .value(1), .blocking(1), .predict(1));

      // Check there hasn't been a JTAG reset while we were clearing the "op in progress" flag. If
      // not, we'll go around again (and read the DMI register again)
      if (jtag_agent_cfg_h.in_reset) begin
        rw_info.status = UVM_NOT_OK;
        return;
      end
    end
  endtask

endclass
