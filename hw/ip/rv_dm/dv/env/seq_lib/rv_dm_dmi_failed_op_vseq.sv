// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_dmi_failed_op_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_dmi_failed_op_vseq)
  `uvm_object_new

  // Returns the value that should be written to the dmi register to request a DMI operation that
  // accesses the register at addr. If op is DmiOpWrite, this operation should write data to the
  // register. If not, the operation is None or should read the register (and ignores the data
  // argument in either case).
  function uvm_reg_data_t make_dmi_reg_op(bit [6:0] addr, bit [31:0] data, jtag_dmi_op_req_e op);
    uvm_reg_data_t ret;
    ret = get_csr_val_with_updated_field(jtag_dtm_ral.dmi.data, '0, data);
    ret = get_csr_val_with_updated_field(jtag_dtm_ral.dmi.op, ret, op);
    ret = get_csr_val_with_updated_field(jtag_dtm_ral.dmi.address, ret, addr);
    return ret;
  endfunction

  // Send a DMI operation and abort it by issuing trst_n. This will cancel the operation, so it will
  // have no effect.
  task send_interrupted_dmi_operation(jtag_dmi_op_req_e op);
    bit [6:0] data0_addr = 4;

    // Issue a JTAG transaction that writes to the dmi register to request a DMI operation that
    // accesses the data0 register (either reading it or writing a random value)
    csr_wr(.ptr(jtag_dtm_ral.dmi),
           .value(make_dmi_reg_op(data0_addr, $urandom, op)),
           .blocking(1));

    // At this point, we've just finished requesting the DMI operation and are on the negedge of
    // tck. The TAP FSM has just got back to RunTestIdle and state_q in dmi_jtag will be Read or
    // Write.
    //
    // Inject a trst_n reset. This will jump state_q back to Idle. This reset will also cause
    // dmi_jtag to send dmi_rst_n, which tells dm_top to drop the transaction. In fact, any DMI
    // write (if op is DmiOpWrite) will be cancelled because the DMI reset gets to dm_csrs faster
    // than the CDC synchronisation for the operation, but it shouldn't really matter.
    cfg.m_jtag_agent_cfg.vif.do_trst_n();

    // At this point, trst_n will no longer be asserted, but we don't know that the JTAG agent
    // config has noticed yet. Wait until its in_reset flag drops, to avoid the next JTAG operation
    // exiting early.
    wait(!cfg.m_jtag_agent_cfg.in_reset);

    // Clear the DMI error by writing 1 to the dmireset field of the dtmcs register.
    csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmireset), .value(1'b1), .blocking(1));
  endtask

  task body();
    bit [6:0] data0_addr = 4;

    uvm_reg_data_t dmi_val;
    bit [31:0] data0_value0 = $urandom(), data0_value1 = $urandom();

    // In order to get a collision below, we need to make sure the JTAG agent doesn't mess around in
    // the RTI state between the two manual writes that we do to the dmi register.
    cfg.m_jtag_agent_cfg.min_rti = 1;

    // Write a known value to data0, which we will read back.
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(data0_value0));

    // As an extra check (since we're doing a detailed investigation of DMI handling in this vseq),
    // send and abort a DMI operation. This steps through a particular edge in the jtag_dmi FSM. We
    // "test that it works" by checking this doesn't interfere with the DMI operations that will
    // follow.
    send_interrupted_dmi_operation($urandom_range(0, 1) ? DmiOpRead : DmiOpWrite);

    // To try to generate a DMI busy error, we start by sending an arbitrary DMI request. We don't
    // want to use jtag_dmi_reg_frontdoor, because that driver has some intentional waits to avoid
    // finishing too quickly. We actively want to finish too quickly!
    //
    // Issue a JTAG transaction that writes to the dmi register to start an operation that will read
    // the contents of the data0 register. The csr_wr task completes when the JTAG transaction has
    // completed, but before the DMI operation has actually happened.
    csr_wr(.ptr(jtag_dtm_ral.dmi),
           .value(make_dmi_reg_op(data0_addr, 0, DmiOpRead)),
           .blocking(1));

    // At this point, the DAP is going to be working through the Read and WaitReadValid states. This
    // takes a bit of time because there is a CDC between the JTAG clock and the system clock for
    // the request and the response.
    //
    // Issue a second conflicting DMI access. This should collide, causing a busy error (and getting
    // dropped). To make it easy to check this has been dropped, the conflicting DMI access is
    // writing a different value to the register.
    csr_wr(.ptr(jtag_dtm_ral.dmi),
           .value(make_dmi_reg_op(data0_addr, data0_value1, DmiOpWrite)),
           .blocking(1));

    // Check that the error has indeed appeared. This is visible as the dmistat field having value 3
    // (described as "an operation was attempted while a DMI access was still in progress")
    check_dmistat(2'h3);

    // Clear the error by writing 1 to the dmireset field of the dtmcs register.
    csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmireset), .value(1'b1), .blocking(1));

    // We should now poll the dmi register to check whether the initial operation has completed. In
    // practice it definitely will have done so by now (very shortly after the DMI write request
    // caused an error).
    //
    // To check this, read from the dmi register. Jtag doesn't really have a concept of a "register
    // read" so instead we implement this by writing a no-op DMI operation (see the
    // get_wdata_for_read() function in jtag_dtm_reg_dmi for the implementation).
    csr_rd(.ptr(jtag_dtm_ral.dmi), .value(dmi_val), .blocking(1));
    `DV_CHECK_EQ(get_field_val(jtag_dtm_ral.dmi.op, dmi_val), 0)

    // That JTAG read of the dmi register was the first after the initial dmi request, so the data
    // field that we read back should be the register value. In particular, it should match the
    // value that we wrote to abstractdata[0] at the start.
    `DV_CHECK_EQ(get_field_val(jtag_dtm_ral.dmi.data, dmi_val), data0_value0)
  endtask

endclass
