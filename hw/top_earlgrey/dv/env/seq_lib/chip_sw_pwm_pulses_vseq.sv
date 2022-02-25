// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_pwm_pulses_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_pwm_pulses_vseq)

  `uvm_object_new
 
  virtual task cpu_init();
    super.cpu_init();
    `uvm_info(`gfn, "JDON:CPU init is done.", UVM_LOW) 
  endtask     

  virtual task body();
    super.body();
    
    `uvm_info(`gfn, "JDON:do nothing body is done.", UVM_LOW)  
  endtask // body
   
endclass // chip_sw_pwm_pulses_vseq
