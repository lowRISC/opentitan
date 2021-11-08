// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_in_out_inverted_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_in_out_inverted_vseq)

  `uvm_object_new

  sysrst_ctrl_item  data_item;

  task body();
  uvm_reg_data_t rdata, rdata1;
    `uvm_info(`gfn, "Starting the body from in_out_inverted_seq", UVM_NONE)
      
    `uvm_info(`gfn, "Inverting the input pins", UVM_NONE)
      
      //Do not override the reset values of ec_rst_l and flash_wp_l
      csr_wr(ral.pin_out_ctl, 'h0);
      csr_wr(ral.pin_allowed_ctl, 'h0);

      //Configuring to invert the input pins
      csr_wr(ral.key_invert_ctl, 32'h55);
      csr_rd(ral.pin_out_ctl, rdata);
      `uvm_info(`gfn, $sformatf("pin out ctl value register reads:%0h", rdata), UVM_NONE)
      csr_rd(ral.pin_allowed_ctl, rdata1);
      `uvm_info(`gfn, $sformatf("pin_allowed_ctl value register read:%0h", rdata1), UVM_NONE)

     repeat (20) begin
      
      //Send randon data to input pins
      `uvm_do_on(m_sysrst_ctrl_in_out_passthrough_seq, p_sequencer.sysrst_ctrl_sequencer_h);
       
      //Output pins should be inverted value of input pins
      @(posedge cfg.m_sysrst_ctrl_agent_cfg.vif.clk_i)
      if ( cfg.m_sysrst_ctrl_agent_cfg.vif.pwrb_out != (~cfg.m_sysrst_ctrl_agent_cfg.vif.pwrb_in) | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key0_out != (~cfg.m_sysrst_ctrl_agent_cfg.vif.key0_in) | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key1_out != (~cfg.m_sysrst_ctrl_agent_cfg.vif.key1_in) | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key2_out != (~cfg.m_sysrst_ctrl_agent_cfg.vif.key2_in)) begin
          `uvm_error(`gfn, "Input pins are not inverted")
      end
     end
     

     `uvm_info(`gfn, "Inverting the output pins", UVM_NONE)

      //Configuring register to invert the output pins
      csr_wr(ral.key_invert_ctl, 32'hAA);

     repeat (20) begin

      //Send randon data to input pins
      `uvm_do_on(m_sysrst_ctrl_in_out_passthrough_seq, p_sequencer.sysrst_ctrl_sequencer_h);
       
      //Output pins should be inverted value of input pins
      if ( cfg.m_sysrst_ctrl_agent_cfg.vif.pwrb_in != (~cfg.m_sysrst_ctrl_agent_cfg.vif.pwrb_out) | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key0_in != (~cfg.m_sysrst_ctrl_agent_cfg.vif.key0_out) | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key1_in != (~cfg.m_sysrst_ctrl_agent_cfg.vif.key1_out) | 
           cfg.m_sysrst_ctrl_agent_cfg.vif.key2_in != (~cfg.m_sysrst_ctrl_agent_cfg.vif.key2_out)) begin
          `uvm_error(`gfn, "Output pins are not inverted")
      end
     end
  endtask : body

endclass : sysrst_ctrl_smoke_vseq