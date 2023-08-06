// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Verify the JTAG has priority over TL for the Mutex
class lc_ctrl_jtag_priority_vseq extends lc_ctrl_jtag_access_vseq;

  `uvm_object_utils(lc_ctrl_jtag_priority_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[1 : 1]};}

  // We expect JTAG to be the mutex owner at the end of the claim phase
  constraint mutex_owner_c {
    mutex_owner_write == LcCtrlJTAG;
    mutex_owner_read == LcCtrlJTAG;
  }

  // Write to a JTAG register directly using the CSR sequence
  task write_jtag_reg_direct(uvm_reg r, uvm_reg_data_t data);
    jtag_riscv_csr_seq csr_seq;
    uvm_reg_addr_t addr = r.get_address();
    `uvm_create_on(csr_seq, p_sequencer.jtag_riscv_sequencer_h)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(csr_seq,
                                   addr == local::addr[jtag_riscv_agent_pkg::DMI_ADDRW + 1 : 0];
        data == local::data[DMI_DATAW - 1 : 0];
        do_write == 1;)
    csr_seq.start(p_sequencer.jtag_riscv_sequencer_h);
  endtask

  // Simultaneous claim via TL and JTAG
  task claim_mutex_simultaneous;
    int tl_delay, tl_delay_incr, jtag_clks, tl_clks;
    `uvm_info(`gfn, $sformatf("claim_mutex_simultaneous: started"), UVM_MEDIUM)

    tl_delay = 0;

    do begin
      // Clear clock counters
      jtag_clks = 0;
      tl_clks   = 0;

      // Release Mutex for both I/F
      // verilog_format: off
      `DV_SPINWAIT(
          fork
            release_mutex(LcCtrlTLUL);
            release_mutex(LcCtrlJTAG);
          join
          )
      // verilog_format: on

      // Ensure eventual convergence by making start point randomized
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 2));

      fork
        // Try to claim from both interfaces
        begin
          write_jtag_reg_direct(.r(m_claim_transition_if), .data(CLAIM_TRANS_VAL));
        end

        begin
          cfg.clk_rst_vif.wait_clks(tl_delay);
          csr_wr(.ptr(m_claim_transition_if), .value(CLAIM_TRANS_VAL), .map(m_map[LcCtrlTLUL]),
                 .blocking(1));
        end

        // Count clocks to active claim signals
        begin : count_jtag_clks
          while (cfg.lc_ctrl_vif.mutex_claim_jtag != 1) begin
            cfg.clk_rst_vif.wait_clks(1);
            jtag_clks++;
          end
        end : count_jtag_clks

        begin : count_tl_clks
          while (cfg.lc_ctrl_vif.mutex_claim_tl != 1) begin
            cfg.clk_rst_vif.wait_clks(1);
            tl_clks++;
          end
        end : count_tl_clks
      join

      // Adjust TL delay so that claims happen simultaneously
      if (jtag_clks > tl_clks) begin
        tl_delay_incr = (jtag_clks - tl_clks) / 2;
        tl_delay_incr = (tl_delay_incr > 0) ? tl_delay_incr : 1;
      end else if (jtag_clks < tl_clks) begin
        tl_delay_incr = (jtag_clks - tl_clks) / 2;
        tl_delay_incr = (tl_delay_incr < 0) ? tl_delay_incr : -1;
      end else tl_delay_incr = 0;

      tl_delay += tl_delay_incr;
      `uvm_info(`gfn, $sformatf(
                {
                  "claim_mutex_simultaneous: tl_delay=%0d tl_delay_incr=%d ",
                  "tl_jtag_clks=%0d tl_clks=%0d"
                },
                tl_delay,
                tl_delay_incr,
                jtag_clks,
                tl_clks
                ), UVM_MEDIUM)
    end while (!(jtag_clks == tl_clks));
  endtask

  // Claim the mutex for the register writes
  virtual task csr_write_mutex_claim;
    uvm_reg_data_t mutex_val = 0;
    `uvm_info(`gfn, $sformatf(
              "csr_write_mutex_claim: claiming mutex for interface %s", mutex_owner_write.name()),
              UVM_MEDIUM)

    `DV_SPINWAIT(claim_mutex_simultaneous();)

    // Check that JTAG has control of the mutex
    csr_rd_check(.ptr(m_claim_transition_if), .compare_value(CLAIM_TRANS_VAL),
                 .map(m_map[LcCtrlJTAG]));

    // Check TL hasn't got control of the mutex
    csr_rd(.ptr(m_claim_transition_if), .value(mutex_val), .map(m_map[LcCtrlTLUL]));
    `DV_CHECK_NE(mutex_val, CLAIM_TRANS_VAL)

    `uvm_info(`gfn, $sformatf(
              "csr_write_mutex_claim: mutex claimed for interface %s", mutex_owner_write.name()),
              UVM_MEDIUM)
  endtask

  // Claim the mutex for the register reads
  virtual task csr_read_mutex_claim;
    uvm_reg_data_t mutex_val = 0;
    `uvm_info(`gfn, $sformatf(
              "csr_read_mutex_claim: claiming mutex for interface %s", mutex_owner_read.name()),
              UVM_MEDIUM)

    `DV_SPINWAIT(claim_mutex_simultaneous();, "wait for simultaneous mutex claim",
                 20_000_000)

    // Check that JTAG has control of the mutex
    csr_rd_check(.ptr(m_claim_transition_if), .compare_value(CLAIM_TRANS_VAL),
                 .map(m_map[LcCtrlJTAG]));

    // Check TL hasn't got control of the mutex
    csr_rd(.ptr(m_claim_transition_if), .value(mutex_val), .map(m_map[LcCtrlTLUL]));
    `DV_CHECK_NE(mutex_val, CLAIM_TRANS_VAL)

    `uvm_info(`gfn, $sformatf(
              "csr_read_mutex_claim: mutex claimed for interface %s", mutex_owner_read.name()),
              UVM_MEDIUM)
  endtask
endclass
