// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_fifo_reset_acq_vseq extends i2c_target_runtime_base_vseq;
  `uvm_object_utils(i2c_target_fifo_reset_acq_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();

    cfg.rd_pct = 0;
//    cfg.rs_pct = 0;
//    cfg.min_data = 10;
//    cfg.max_data = 20;
    cfg.m_i2c_agent_cfg.taget_fifo_reset_test_mode = 1;
    seq_runtime = 500;
  endtask

  task test_event();
    #50us;
    repeat (5) begin
      `JDBG(("assa dir stop driver"))
      // stop driver
      pause_acq_read = 1;
      cfg.m_i2c_agent_cfg.agent_reset = 1;
      m_i2c_host_seq.seq_stop();

      // flush acq
      ral.fifo_ctrl.acqrst.set(1'b1);
      csr_update(ral.fifo_ctrl);
      `JDBG(("assa dir clean fifo"))

      // clean up sb
      cfg.scb_h.target_mode_wr_exp_fifo.flush();
      cfg.scb_h.target_mode_wr_obs_fifo.flush();
      cfg.scb_h.obs_wr_id = 0;

      tran_id = 0;

      #10us;
      cfg.scb_h.skip_rs = 1;
      cfg.m_i2c_agent_cfg.agent_reset = 0;
      pause_acq_read = 0;

      `JDBG(("assa dir resume driver"))
      #($urandom_range(1, 5) * 10us);
    end
  endtask // test_event

  task proc_itnr_cmd_complete();
    // read acq fifo in 'body' task
    clear_interrupt(CmdComplete, 0);
  endtask // proc_itnr_cmd_complete

  task process_acq();
    bit fifo_empty, pop_all;
    int delay;

    while (!cfg.stop_intr_handler) begin
      delay = $urandom_range(0, 10);
      cfg.clk_rst_vif.wait_clks( delay * acq_rd_cyc);
      // pop one all entries by 25% of chance.
      pop_all = ($urandom_range(0,3) > 0);
      if (!pause_acq_read) read_acq_fifo(~pop_all, fifo_empty);
    end
  endtask // process_acq
endclass // i2c_target_fifo_reset_acq_vseq
