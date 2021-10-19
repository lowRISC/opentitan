// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Polled filters test sequence
class adc_ctrl_filters_polled_vseq extends adc_ctrl_base_vseq;
  
  `uvm_object_utils(adc_ctrl_filters_polled_vseq)


  `uvm_object_new
  
  task body();
    uvm_reg_data_t rdata;

    // Make sure ADC is off
    csr_wr(ral.adc_en_ctl,'h0);

    // Set up filters from config object values
    configure_filters();

    // Set one shot interrupt enable
    //csr_wr(ral.adc_intr_ctl, onehot_intr);
    
    repeat(1) begin

      // Clear interrupt status reg
      csr_wr(ral.adc_intr_status, '1);
      
      // Check interrupt status
      csr_rd(ral.adc_intr_status,rdata);
      if(rdata != 0)
        `uvm_error(`gfn, $sformatf("Interrupt status not cleared (%x)", rdata))
      `uvm_info(`gfn, ral.adc_intr_status.sprint(), UVM_HIGH)


      // Start ADC 
      ral.adc_en_ctl.adc_enable.set(1);
      ral.adc_en_ctl.oneshot_mode.set(0);
      csr_wr(ral.adc_en_ctl, ral.adc_en_ctl.get());

      // Send random data via AST ADC agent
      `uvm_do_on_with(m_ast_adc_random_ramp_seq, 
        p_sequencer.ast_adc_sequencer_h,{
        ramp_min      == 0;
        ramp_max      == ast_adc_value_t'('1);
        // ramp_max == 100;
        ramp_step_min == 1;
        ramp_step_max == 20;
        ramp_rising   == 1;
      })

      // Send random data via AST ADC agent
      `uvm_do_on_with(m_ast_adc_random_ramp_seq, 
        p_sequencer.ast_adc_sequencer_h,{
        ramp_min      == 0;
        ramp_max      == ast_adc_value_t'('1);
        // ramp_max == 100;
        ramp_step_min == 1;
        ramp_step_max == 20;
        ramp_rising   == 0;
      })

      // Give time to settle
      #500us;
      `uvm_info(`gfn, $sformatf("adc_en_ctl=%0x", 
            ral.adc_en_ctl.get()),UVM_HIGH)


      // Check interrupt status
      csr_rd(ral.adc_intr_status,rdata);
      `uvm_info(`gfn,ral.adc_intr_status.sprint(),UVM_HIGH)

      
      // if(ral.adc_intr_status.get() != onehot_intr)
      //   `uvm_error(`gfn, 
      //     $sformatf("Interrupt status error - expected %x got %x", 
      //       onehot_intr[31:0], rdata[31:0]))


      // Read and check ADC value registers
      csr_rd(ral.adc_chn_val[0],rdata);
      `uvm_info(`gfn, $sformatf("adc_chn_val[0] reads %x",rdata[31:0]),UVM_HIGH)

      csr_rd(ral.adc_chn_val[1],rdata);
      `uvm_info(`gfn, $sformatf("adc_chn_val[1] reads %x",rdata[31:0]),UVM_HIGH)
      
  
      
      `uvm_info(`gfn, ral.adc_chn_val[0].sprint(),UVM_HIGH)
      `uvm_info(`gfn, ral.adc_chn_val[1].sprint(),UVM_HIGH)

      `uvm_info(`gfn, cfg.m_ast_adc_agent_cfg.sprint(),UVM_HIGH)

      // Turn off ADC 
      csr_wr(ral.adc_en_ctl,'h0);

    end

    // Allow time for sim to finish or we trigger an assertion
    #100us;
  endtask : body

endclass : adc_ctrl_filters_polled_vseq
