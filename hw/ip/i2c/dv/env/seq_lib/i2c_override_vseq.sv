// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_override_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_override_vseq)

  rand bit sclval;
  rand bit sdaval;
  rand bit txovrden;

  `uvm_object_new

  virtual task body();
    // disable i2c_monitor and i2c_scoreboard since they can not handle this test
    `uvm_info(`gfn, "disable i2c_monitor and i2c_scoreboard", UVM_DEBUG)
    cfg.m_i2c_agent_cfg.en_monitor = 1'b0;
    cfg.en_scb = 1'b0;

    // disable clear_all_interrupts task due to abnormal assertion of interrupts
    do_clear_all_interrupts = 1'b0;

    device_init();
    host_init();

    for (uint cur_tran = 1; cur_tran <= num_trans; cur_tran++) begin
      `uvm_info(`gfn, $sformatf("\nTransaction %0d", cur_tran), UVM_DEBUG)
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
        cfg.m_i2c_agent_cfg.vif.wait_for_dly(1);  // fast enough
        `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.scl_i, sclval)
        `DV_CHECK_EQ(cfg.m_i2c_agent_cfg.vif.sda_i, sdaval)
        `uvm_info(`gfn,
                  $sformatf("\n  scl_i %0b sclval %0b", cfg.m_i2c_agent_cfg.vif.scl_i, sclval),
                  UVM_DEBUG)
        `uvm_info(`gfn,
                  $sformatf("\n  sda_i %0b sdaval %0b", cfg.m_i2c_agent_cfg.vif.sda_i, sdaval),
                  UVM_DEBUG)
      end
    end
  endtask : body

endclass : i2c_override_vseq
