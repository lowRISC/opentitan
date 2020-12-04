// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic stretch_timeout test vseq
class i2c_stretch_timeout_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_stretch_timeout_vseq)
  `uvm_object_new

  // set timeout field to minimum value to ensure
  // stretch_timeout irq is asserted for every target's ACK
  constraint t_timeout_c { t_timeout == 1; }

  // timeout is always enabled so stretch_timeout irq is aggressively asserted
  constraint e_timeout_c { e_timeout == 1; }

  local uint cnt_wr_stretch;
  local uint cnt_rd_stretch;
  local bit  check_wr_stretch;
  local bit  check_rd_stretch;

  virtual task body();
    `uvm_info(`gfn, "\n--> start of i2c_stretch_timeout_vseq", UVM_DEBUG)
    initialization();
    for (int i = 1; i <= num_trans; i++) begin
      cnt_wr_stretch = 0;
      cnt_rd_stretch = 0;
      check_wr_stretch = 1'b0;
      check_rd_stretch = 1'b0;

      `uvm_info(`gfn, $sformatf("\n  run simulation %0d/%0d", i, num_trans), UVM_DEBUG)
      fork
        begin
          check_wr_stretch = 1'b1;
          host_send_trans(1, WriteOnly);
          check_wr_stretch = 1'b0;
          if (!cfg.under_reset) begin
            // host clock is stretched for every target's ACK thus
            // cnt_wr_stretch must be equal to (num_wr_bytes + 1)
            // adding 1 is for the target's ACK to the response address byte sent by host
            `DV_CHECK_EQ(cnt_wr_stretch, (num_wr_bytes + 1))
          end

          check_rd_stretch = 1'b1;
          host_send_trans(1, ReadOnly);
          check_rd_stretch = 1'b0;
          if (!cfg.under_reset) begin
            // check_rd_stretchretch_timeout must be equal to 1
            // that is the target's ACK to response the address byte sent by host
            `DV_CHECK_EQ(cnt_rd_stretch, 1)
          end
        end
        begin
          while (!cfg.under_reset &&
                 (check_wr_stretch || check_rd_stretch)) process_stretch_timeout_intr();
        end
      join
    end
    `uvm_info(`gfn, "\n--> end of i2c_stretch_timeout_vseq", UVM_DEBUG)
  endtask : body

  task process_stretch_timeout_intr();
    bit stretch_timeout;

    csr_rd(.ptr(ral.intr_state.stretch_timeout), .value(stretch_timeout));
    if (stretch_timeout) begin
      if (check_wr_stretch) cnt_wr_stretch++;
      if (check_rd_stretch) cnt_rd_stretch++;

      // must wait stretch_timeout event passes (scl_i is deasserted)
      // before clearing irq otherwise stretch_timeout irq can be re-triggered
      // within clock pulses that interferes the counters
      wait(!cfg.m_i2c_agent_cfg.vif.scl_i);
      clear_interrupt(StretchTimeout);
      `uvm_info(`gfn, $sformatf("\n  check_wr_st %b cnt_wr_st %0d, check_rd_st %b, cnt_rd_st %0d",
          check_wr_stretch, cnt_wr_stretch, check_rd_stretch, cnt_rd_stretch), UVM_DEBUG)
    end
  endtask : process_stretch_timeout_intr

endclass : i2c_stretch_timeout_vseq
