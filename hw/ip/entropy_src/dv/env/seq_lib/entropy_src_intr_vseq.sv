// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test entropy_src interrupts

class entropy_src_intr_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_intr_vseq)

  `uvm_object_new

  push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)          m_rng_push_seq;
  push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_csrng_pull_seq;

  task test_es_entropy_valid();
    // Turn off the dut while we write to its registers.
    disable_dut();
    // Route the entropy to the SW output.
    csr_wr(.ptr(ral.entropy_control.es_route), .value(prim_mubi_pkg::MuBi4True));
    // Turn off ov mode since we don't need to observe the post helth test entropy
    // and don't want to insert entropy via the register FW_OV_WR_DATA.
    csr_wr(.ptr(ral.fw_ov_control), .value(32'h99));
    // Allow for entropy to be read via the SW register.
    csr_wr(.ptr(ral.conf.entropy_data_reg_enable), .value(prim_mubi_pkg::MuBi4True));
    // Enable only entropy valid interrupts.
    csr_wr(.ptr(ral.intr_enable), .value(1 << EntropyValid));
    // Turn on the DUT.
    enable_dut();

    // Create and start rng host sequence.
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);

    // Wait for the entropy_valid interrupt.
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));
    // Expect and clear interrupt bit for entropy valid interrupts.
    check_interrupts(.interrupts((1 << EntropyValid)), .check_set(1'b1));
  endtask // test_es_entropy_valid

  task test_es_observe_fifo_ready();
    // Turn off the dut while we write to its registers.
    disable_dut();
    // Turn on firmware override mode to be able to read from the observe FIFO.
    csr_wr(.ptr(ral.fw_ov_control.fw_ov_mode), .value(prim_mubi_pkg::MuBi4True));
    // Set the observe fifo depth threshold to a low number to trigger the interrupt faster.
    csr_wr(.ptr(ral.observe_fifo_thresh.observe_fifo_thresh), .value(7'b0000100));
    // Enable only es_observe_fifo_ready interrupts.
    csr_wr(.ptr(ral.intr_enable), .value(1 << ObserveFifoReady));
    // Turn on the DUT.
    enable_dut();

    // Create and start rng host sequence.
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);

    // Wait for the observe_fifo_ready interrupt.
    csr_spinwait(.ptr(ral.intr_state.es_observe_fifo_ready), .exp_data(1'b1));
    // Expect and clear interrupt bit for observe FIFO ready interrupts.
    check_interrupts(.interrupts((1 << ObserveFifoReady)), .check_set(1'b1));
  endtask // test_es_observe_fifo_ready

  task body();
    // Test es_entropy_valid interrupt
    test_es_entropy_valid();
    // Test es_observe_fifo_ready interrupt
    test_es_observe_fifo_ready();
    // Disable entropy_src
    disable_dut();

  endtask : body

endclass : entropy_src_intr_vseq
