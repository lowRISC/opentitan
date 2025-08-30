// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send a randomized stream of data through the DOE_INTR_MSG_ADDR/DATA registers from the SoC
// to the RoT, since this is just a direct Read Only channel and has no directly observable
// impact on DUT outputs.
// (The supplied _ADDR and _DATA values are intended to be used by firmware via another
//  channel that is not present at block level.)

class mbx_doe_intr_msg_vseq extends mbx_base_vseq;

  `uvm_object_utils(mbx_doe_intr_msg_vseq)
  `uvm_object_new

  // We want to see all 64 bits (2 x 32-bit registers) in both states over 5 runs so we need to use
  // a reasonable number of randomized values.
  localparam int unsigned NumRandWords = 'h400;
  // Array of random addresses and data to be sent and checked.
  rand bit [top_pkg::TL_DW-2:0] addr[NumRandWords]; // Leave MSB unused, to indicate changes.
  rand bit [top_pkg::TL_DW-1:0] data[NumRandWords]; // Randomize all data bits.

  // Send the randomized data from the SoC side.
  task send_data;
    uvm_reg_data_t init_val;
    // Check that we are starting with a MSB-clear register value; the post-reset state of
    // these registers is zero.
    csr_rd(m_mbx_soc_ral.soc_doe_intr_msg_addr, init_val);
    `DV_CHECK_EQ(init_val[top_pkg::TL_DW-1], 1'b0,
                 "SOC_DOE_INTR_MSG_ADDR does not have expected initial state")
    foreach (data[i]) begin
      // Supply data before the address so that it will be available when the address changes.
      csr_wr(m_mbx_soc_ral.soc_doe_intr_msg_data, data[i]);
      // Supply the address and toggle the MSB of the register to mark the change.
      csr_wr(m_mbx_soc_ral.soc_doe_intr_msg_addr, {!i[0], addr[i]});
      // This is pretty arbitrary but must exceed the maximum delays in CSR accesses so that
      // the RoT side doesn't miss anything.
      delay($urandom_range('h3f, 'h20));
    end
  endtask

  // Retrieve and check the randomized data on the RoT side.
  task check_data;
    uvm_reg_data_t act_addr, act_data;
    for (int unsigned i = 0; i < NumRandWords; i++) begin
      // Await a change in the MSB of the address indicating the availability of a new value pair.
      do csr_rd(ral.doe_intr_msg_addr, act_addr);
      while (act_addr[top_pkg::TL_DW-1] == i[0]); // When the MSB changes the sequence has advanced.
      // The data was sent before the address, so it should already be valid.
      csr_rd(ral.doe_intr_msg_data, act_data);
      // Check both values against expectations.
      // TODO: Ideally we'd leave the scoreboard to check against a prediction but presently we
      // there is no loosely-timed model of register changes and the values can briefly differ on
      // the RoT and SoC sides.
      `DV_CHECK_EQ(act_addr, {!i[0], addr[i]}, "DOE_INTR_MSG_ADDR does not have the expected value")
      `DV_CHECK_EQ(act_data, data[i], "DOE_INTR_MSG_DATA does not have the expected value")
    end
  endtask

  virtual task body();
    `uvm_info(`gfn, "body -- doe_intr_msg test -- Start", UVM_DEBUG)
    fork
      send_data();
      check_data();
    join
    `uvm_info(`gfn, "body -- doe_intr_msg test -- End", UVM_DEBUG)
  endtask

endclass : mbx_doe_intr_msg_vseq
