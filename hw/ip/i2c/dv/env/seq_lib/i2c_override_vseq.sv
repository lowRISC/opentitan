// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test TX override feature through i2c.OVRD and check the pin
class i2c_override_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_override_vseq)

  rand uint  dly_b2b_trans;
  rand uint  num_runs;
  rand bit   sclval;
  rand bit   sdaval;

  bit        en_ovrd  = 1'b1;
  bit        txovrden = 1'b1;
  bit [2:0]  exp_ovrd;

  constraint num_runs_c       { num_runs inside {[5:20]};     }
  constraint sclval_c         { sclval   inside {[0:1]};      }
  constraint sdaval_c         { sdaval   inside {[0:1]};      }
  constraint dly_b2b_trans_c  { dly_b2b_trans inside {[0:1]}; }

  `uvm_object_new

  task pre_start();
    super.pre_start();
    num_runs.rand_mode(0);

    // disable interrupt test
    do_interrupt = 1'b0;
  endtask : pre_start

  // main body
  task body();
    fork
      program_ovrd_reg();
    join
  endtask: body

  // add orvd test on tx and make sure no side-effect on rx
  task program_ovrd_reg();
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `DV_CHECK_STD_RANDOMIZE_FATAL(sclval)
      `DV_CHECK_STD_RANDOMIZE_FATAL(sdaval)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_b2b_trans)

      // disable monitor since it can not handle this test corner
      i2c_monitor_ctrl(1'b0);

      if (cfg.m_i2c_agent_cfg.en_tx_monitor === 1'b1)
        `uvm_fatal(`gfn, "failed due to enabling en_tx_monitor")
      if (cfg.m_i2c_agent_cfg.en_rx_monitor === 1'b1)
        `uvm_fatal(`gfn, "failed due to enabling en_rx_monitor")

      if (en_ovrd && txovrden) begin
        `DV_CHECK_EQ(txovrden, 1);
        `DV_CHECK_EQ(en_ovrd, 1);
        `uvm_info(`gtn, $sformatf("enable ovrd, txovrden: %b", txovrden), UVM_LOW)

        //csr_wr(.csr(ral.ovrd), .value({sdaval, sclval, txovrden}));
        ral.ovrd.txovrden.set(txovrden);
        ral.ovrd.sclval.set(sclval);
        ral.ovrd.sdaval.set(sdaval);
        csr_update(ral.ovrd);
        csr_rd(.ptr(ral.ovrd), .value(exp_ovrd));
        cfg.clk_rst_vif.wait_clks(1);
        `DV_CHECK_EQ(exp_ovrd, {sdaval, sclval, txovrden});

        if (sclval)
          `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.scl_i, 1'bz)
        else
          `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.scl_i, 1'b0)

        if (sdaval)
          `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.sda_i, 1'bz)
        else
          `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.sda_i, 1'b0)

        cfg.clk_rst_vif.wait_clks(dly_b2b_trans);

        // disable ovrd
        csr_wr(.csr(ral.ovrd), .value(0));
        cfg.clk_rst_vif.wait_clks(1);
        csr_rd(.ptr(ral.ovrd), .value(exp_ovrd));

        `DV_CHECK_EQ(exp_ovrd, 0);
        `uvm_info(`gtn, $sformatf("disable ovrd txovrden: %b", exp_ovrd[0]), UVM_LOW)
        `uvm_info(`gtn, $sformatf("finished run %0d/%0d",i, num_trans), UVM_LOW)
      end
    end

  endtask : program_ovrd_reg

  task post_start();
    `uvm_info(`gfn, "stop simulation", UVM_DEBUG)
  endtask : post_start

  // read interrupts and randomly clear interrupts if set
  task process_interrupts();
    // TODO
  endtask : process_interrupts

endclass : i2c_override_vseq
