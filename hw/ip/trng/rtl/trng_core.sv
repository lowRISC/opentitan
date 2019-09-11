// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: TRNG core module
//

module trng_core (
  input                  clk_i,
  input                  rst_ni,

  input  trng_reg_pkg::trng_reg2hw_t reg2hw,
  output trng_reg_pkg::trng_hw2reg_t hw2reg,

  output logic           intr_no_random_num_o 
  output logic           intr_stub_err_o 
);

  // TODO: same as in spi_device.sv, add input scanmode_i to module
  logic scanmode_i;
  assign scanmode_i = 1'b0;

  import trng_reg_pkg::*;

  logic   [31:0]  lfsr_value;
  logic   [31:0]  seed_value;
  logic           event_no_random_num;
  logic           event_stub_err;
  logic           sample_lfsr;


  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------

  prim_intr_hw #(.Width(1)) intr_hw_no_random_num (
    .event_intr_i           (event_no_random_num),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.no_random_num.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.no_random_num.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.no_random_num.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.no_random_num.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.no_random_num.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.no_random_num.d),
    .intr_o                 (intr_no_random_num_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_stub_err (
    .event_intr_i           (event_stub_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.stub_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.stub_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.stub_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.stub_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.stub_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.stub_err.d),
    .intr_o                 (intr_stub_err_o)
  );


  //--------------------------------------------
  // lfsr example random number generator
  //--------------------------------------------

  trng_lfsr u_trng_lfsr (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .load_seed_i    (~reg2hw.ctrl.prng.q),
    .seed_value_i   (seed_value),
    .incr_lfsr_i    (reg2hw.ctrl.prng.q),
    .lfsr_value_o   (lfsr_value)
  );

  // set the random number to the read reg
  assign hw2reg.rnum.d = lfsr_value;

  // seed register
  assign seed_value = reg2hw.seed.q;
  assign hw2reg.seed.d = seed_value;
  assign hw2reg.seed.de = 1'b0; // TODO: how to handle this

  // set the interrupt event when enabled
  assign event_no_random_num = reg2hw.ctrl.prng.q ? sample_lfsr : 1'b0;

  // TODO: sample the lfsr logic for changing values
  assign sample_lfsr = 1'b0; 

  // set the stub interrupt
  assign event_stub_err = 1'b0;

  //--------------------------------------------
  // status
  //--------------------------------------------

  // TODO: create real status here
  assign hw2reg.status.prng.d = 1'b1;
  assign hw2reg.status.trng.d = 1'b0;
  

endmodule
