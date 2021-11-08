// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_combo_detect_ec_rst_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_ec_rst_vseq)

  `uvm_object_new

  sysrst_ctrl_item  data_item;

  task body();
  uvm_reg_data_t rdata, rdata1;
    `uvm_info(`gfn, "Starting the body from combo detect ec_rst", UVM_NONE)
      
  
      //Trigger the input pins
      csr_wr(ral.com_sel_ctl[0], 32'hB); 

      //Set the duration for which the above keys are pressed
      csr_wr(ral.com_det_ctl[0], 32'h3c);
      
      //ec_rst_l interrupt action defined
      csr_wr(ral.com_out_ctl[0], 32'h4);

      //Set the ec_rst_l signal pulse width
      csr_wr(ral.ec_rst_ctl, 32'h64);
      
      
   endtask : body

endclass : sysrst_ctrl_smoke_vseq