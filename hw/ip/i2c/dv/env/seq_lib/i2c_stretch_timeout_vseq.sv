// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic stretch_timeout test vseq
class i2c_stretch_timeout_vseq extends i2c_sanity_vseq;
  `uvm_object_utils(i2c_stretch_timeout_vseq)
  `uvm_object_new

  // set timeout field to minimum value to ensure
  // stretch_timeout irq is asserted for every target's ACK
  constraint t_timeout_c {t_timeout == 1;}

  // timeout is always enabled so stretch_timeout irq is aggressively asserted
  constraint e_timeout_c {e_timeout == 1;}

  local uint num_wr_st;
  local uint num_rd_st;
  local bit check_wr_st;
  local bit check_rd_st;

  virtual task body();

    device_init();
    host_init();

    for (int i = 0; i < num_trans; i++) begin
      num_wr_st = 0;
      num_rd_st = 0;
      check_wr_st = 1'b0;
      check_rd_st = 1'b0;

      fork
        begin
          check_wr_st = 1'b1;
          host_send_trans(.num_trans(1), .trans_type(WriteOnly));
          csr_spinwait(.ptr(ral.status.fmtempty), .exp_data(1'b1));
          check_wr_st = 1'b0;
          `uvm_info(`gfn, $sformatf("\ncheck_wr_st %0d", check_wr_st), UVM_DEBUG)
          // host clock is stretched for every target's ACK thus
          // num_wr_st must be equal to (num_wr_bytes + 1)
          // adding 1 is for the target's ACK to the response address byte sent by host
          `DV_CHECK_EQ(num_wr_st, (num_wr_bytes + 1))

          check_rd_st = 1'b1;
          host_send_trans(.num_trans(1), .trans_type(ReadOnly));
          csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b1));
          check_rd_st = 1'b0;
          `uvm_info(`gfn, $sformatf("\ncheck_rd_st %0d", check_rd_st), UVM_DEBUG)
          // check_rd_stretch_timeout must be equal to 1
          // that is the target's ACK to response the address byte sent by host
          `DV_CHECK_EQ(num_rd_st, 1)
        end
        begin
          while (check_wr_st || check_rd_st) check_wr_st_intr();
        end
      join
    end
  endtask : body

  task check_wr_st_intr();
    bit stretch_timeout;

    csr_rd(.ptr(ral.intr_state.stretch_timeout), .value(stretch_timeout));
    if (stretch_timeout) begin
      if (check_wr_st) num_wr_st++;
      if (check_rd_st) num_rd_st++;

      // must wait stretch_timeout event passes (scl_i is deasserted)
      // before clearing irq otherwise stretch_timeout irq can be re-triggered
      // within clock pulses that interferes the counters
      wait(!cfg.m_i2c_agent_cfg.vif.scl_i);
      clear_interrupt(StretchTimeout);
      `uvm_info(`gfn, $sformatf("\ncheck_wr_st %0d, check_rd_st %0d", num_wr_st, num_rd_st),
                UVM_DEBUG)
    end
  endtask : check_wr_st_intr

endclass : i2c_stretch_timeout_vseq
