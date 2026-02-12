// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A simple sequence to exercise the conditional updating of `rxenable_out` that controls
// the reception of OUT transactions on endpoints. Conditional updating is required to
// prevent a race between software enabling OUT reception on anendpoint at the moment that
// hardware disables it on another.
// This sequence tests only the CSR-side behavior.

class usbdev_rxenable_out_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rxenable_out_vseq)

  `uvm_object_new

  // Collect endpoint count from the DUT description.
  localparam int unsigned NEndpoints = usbdev_reg_pkg::NEndpoints;

  task body();
    uvm_reg_data_t ep_odd = {((NEndpoints+1)/2){2'b10}}; // AAA
    uvm_reg_data_t ep_even = ep_odd >> 1; // 555
    uvm_reg_data_t ep_all = {NEndpoints{1'b1}};
    uvm_reg_data_t exp_data;
    uvm_reg_data_t rd_data;

    // Basic test of `rxenable_out` CSR behavior without interference from the USB itself.
    csr_wr(.ptr(ral.rxenable_out), .value(ep_all));
    csr_rd(.ptr(ral.rxenable_out), .value(rd_data));
    `DV_CHECK_EQ_FATAL(rd_data, ep_all)
    `uvm_info(`gfn, "Completed basic test of setting rxevent_out", UVM_MEDIUM)

    // Attempt to clear the enable bit of every other output.
    csr_wr(.ptr(ral.rxenable_out), .value(ep_odd << 16));
    csr_rd(.ptr(ral.rxenable_out), .value(rd_data));
    `DV_CHECK_EQ_FATAL(rd_data, ep_odd)
    `uvm_info(`gfn, "Completed basic text of conditional clearing rxevent_out", UVM_MEDIUM)

    // Attempt to invert all of the enable bits.
    csr_wr(.ptr(ral.rxenable_out), .value(rd_data ^ ep_all));
    csr_rd(.ptr(ral.rxenable_out), .value(rd_data));
    `DV_CHECK_EQ_FATAL(rd_data, ep_even)
    `uvm_info(`gfn, "Completed basic test of inverting data toggles", UVM_MEDIUM)

    // Clear them all before starting.
    csr_wr(.ptr(ral.rxenable_out), .value(0));
    exp_data = 0;

    for (int unsigned txn = 0; txn < num_trans; txn++) begin
      bit [NEndpoints-1:0] change;
      bit [NEndpoints-1:0] enable;
      uvm_reg_data_t wr_data;

      // Randomly modify the OUT enables and update our expectations.
      change = $urandom & ep_all;
      enable = change & $urandom & ep_all;
      `uvm_info(`gfn, $sformatf("Changing 0x%04x to 0x%04x", change, enable), UVM_MEDIUM)
      // Update our expectation.
      exp_data |= (change & enable);  // Endpoints we are enabling.
      exp_data &= ep_all & ~(change & ~enable);  // Endpoints we are disabling.

      // Present random state to the endpoints that we are not changing; it should be ignored by
      // the device.
      // Note: the upper bits specify which bits are to be _preserved_, i.e. set = 'do not change.'
      wr_data = (~change << 16) | enable | ($urandom & ep_all & (change ^ ep_all));
      csr_wr(.ptr(ral.rxenable_out), .value(wr_data));
      csr_rd(.ptr(ral.rxenable_out), .value(rd_data));

      // Check against expectations.
      `DV_CHECK_EQ_FATAL(rd_data, exp_data)
    end
  endtask

endclass
