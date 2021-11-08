// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class sysrst_ctrl_smoke_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_smoke_vseq)

  `uvm_object_new

  sysrst_ctrl_item  data_item;

  task body();
    `uvm_info(`gfn, "Starting the body from smoke_vseq", UVM_NONE)
      
     repeat (20) begin

      //Send randon data to input pins
      `uvm_do_on(m_sysrst_ctrl_in_out_passthrough_seq, p_sequencer.sysrst_ctrl_sequencer_h);
       
      //In normal mode, sysrst_ctrl will pass the input pin information to output pins
      if ( cfg.m_sysrst_ctrl_agent_cfg.vif.pwrb_in != cfg.m_sysrst_ctrl_agent_cfg.vif.pwrb_out | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key0_in != cfg.m_sysrst_ctrl_agent_cfg.vif.key0_out | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key1_in != cfg.m_sysrst_ctrl_agent_cfg.vif.key1_out | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key2_in != cfg.m_sysrst_ctrl_agent_cfg.vif.key2_out) begin
          `uvm_error(`gfn, "In Normal mode input pins is not equal to output pins")
      end
     end
  endtask : body

endclass : sysrst_ctrl_smoke_vseq
