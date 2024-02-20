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

    // Wait 10 tck cycles to allow the DMI req to complete. If we read the DTM DMI register too
    // soon, it may end up setting the in progress sticky bit, causing more time wasted.
    jtag_agent_cfg_h.vif.wait_tck(10);

    // Poll for completion.
    `DV_SPINWAIT_EXIT(
      read_dmi_over_jtag(jtag_dtm_ral, csr_or_fld);,
      begin
        fork
          wait(jtag_agent_cfg_h.in_reset);
          // TODO: Make timeout more configurable.
          `DV_WAIT_TIMEOUT(jtag_agent_cfg_h.vif.tck_period_ps * 10_000_000 /*10 ms*/)
        join_any
      end
    )

    `uvm_info(`gfn, $sformatf("DMI CSR req completed: %0s", rw_info.convert2string()), UVM_HIGH)
    jtag_dtm_ral_sem_h.put();
  endtask

  // Use JTAG to read the contents of the DMI register
  //
  // If the underlying operation in rw_info is UVM_READ, this also updates rw_info.value to contain
  // the requested register contents.
  //
  // For either direction (read or write), it waits until the DMI is running an operation.
  task read_dmi_over_jtag(jtag_dtm_reg_block jtag_dtm_ral, csr_field_t csr_or_fld);
    uvm_reg_data_t    dmi_data_rdata;
    jtag_dmi_op_rsp_e op_rsp;
    int               num_dones_seen = 0;

    // This loop works around a confusing situation where TCK is running much faster than the main
    // clock and the first JTAG read responds with DmiOpOk just as it discovers (too late) that
    // there was actually an operation in progress. The next JTAG read correctly responds with
    // DmiOpInProgress and the operation is done next time we see DmiOpOk (or DmiOpFailed).
    //
    // If we see two results other than DmiOpInProgress, we know that the operation is genuinely
    // finished.
    while (num_dones_seen < 2) begin
      uvm_reg_data_t rdata;

      csr_rd(.ptr(jtag_dtm_ral.dmi), .value(rdata), .blocking(1));
      op_rsp = jtag_dmi_op_rsp_e'(get_field_val(jtag_dtm_ral.dmi.op, rdata));

      // If DMI responds with DmiOpInProgress, it is telling us that an operation was running. That
      // flag is sticky, so we need to follow up by writing 1 to "dmireset" over JTAG to clear the
      // flag.
      if (op_rsp == DmiOpInProgress) begin
        csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmireset), .value(1), .blocking(1), .predict(1));
      end else begin
        if (num_dones_seen == 0) begin
          dmi_data_rdata = get_field_val(jtag_dtm_ral.dmi.data, rdata);
        end

        num_dones_seen++;
      end
    end

    // At this point, we've seen two reads where op_rsp is not DmiOpInProgress. Use the results of
    // the second read to populate rw_info. If we are doing a UVM_READ, this includes extracting the
    // CSR or field from rdata.
    rw_info.status = op_rsp == DmiOpOk ? UVM_IS_OK : UVM_NOT_OK;
    if (rw_info.kind == UVM_READ) begin
      if (csr_or_fld.field != null) begin
        dmi_data_rdata = get_field_val(csr_or_fld.field, dmi_data_rdata);
      end

      rw_info.value = new[1];
      rw_info.value[0] = dmi_data_rdata;
    end
  endtask

endclass
