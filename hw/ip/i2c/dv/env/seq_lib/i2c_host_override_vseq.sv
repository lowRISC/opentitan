// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_host_override_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_host_override_vseq)
  `uvm_object_new

  local rand bit sclval;
  local rand bit sdaval;
  local rand bit txovrden;

  constraint txovrden_c { txovrden dist {1 := 1, 0 := 1}; }
  constraint sclval_c { sclval dist {1 := 1, 0 := 1}; }
  constraint sdaval_c { sdaval dist {1 := 1, 0 := 1}; }

  task pre_start();
    super.pre_start();
    // for this vseq, $value$plusargs "+en_scb=0" is defined in i2c_sim_cfg.hjson
    // disable i2c_monitor and i2c_scoreboard since they can not handle this test
    // disable clear_all_interrupts task due to abnormal assertion of interrupts
    do_clear_all_interrupts = 1'b0;
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  task body();
    initialization();
    `uvm_info(`gfn, "\n--> start of i2c_host_override_vseq", UVM_DEBUG)
    for (uint i = 1; i <= num_trans; i++) begin
      bit [TL_DW-1:0] reg_val;
      `uvm_info(`gfn, $sformatf("\n  run simulation %0d/%0d", i, num_trans), UVM_DEBUG)
      `uvm_info(`gfn, $sformatf("override val = %0d",{txovrden,sclval,sdaval}), UVM_MEDIUM)
      // program to enable OVRD reg
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(sclval)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(sdaval)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(txovrden)
      ral.ovrd.txovrden.set(txovrden);
      ral.ovrd.sclval.set(sclval);
      ral.ovrd.sdaval.set(sdaval);
      csr_update(ral.ovrd);

      // checking DUT's scl and sda
      if (txovrden) begin
        cfg.m_i2c_agent_cfg.vif.wait_for_dly(1); // fast enough
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.scl_i, sclval)
          `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.sda_i, sdaval)
          `uvm_info(`gfn, $sformatf("\n  scl_i %0b sclval %0b",
              cfg.m_i2c_agent_cfg.vif.scl_i, sclval), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf("\n  sda_i %0b sdaval %0b",
              cfg.m_i2c_agent_cfg.vif.sda_i, sdaval), UVM_DEBUG)
        end
      end
      // Read override register values
      csr_rd(.ptr(ral.ovrd), .value(reg_val));
    end
    `uvm_info(`gfn, "\n--> end of i2c_host_override_vseq", UVM_DEBUG)
  endtask : body

endclass : i2c_host_override_vseq
