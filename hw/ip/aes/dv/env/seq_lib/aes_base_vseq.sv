// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


class aes_base_vseq extends cip_base_vseq #(
  .CFG_T               (aes_env_cfg),
  .RAL_T               (aes_reg_block),
  .COV_T               (aes_env_cov),
  .VIRTUAL_SEQUENCER_T (aes_virtual_sequencer)
);
  
  `uvm_object_utils(aes_base_vseq)
  `uvm_object_new
  parameter ENCRYPT = 1'b0;
  parameter DECRYPT = 1'b1;
  
  aes_reg2hw_t aes_reg;

  // various knobs to enable certain routines
  bit do_aes_init = 1'b1;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_aes_init) aes_init();
  endtask

  virtual task dut_shutdown();
    // check for pending aes operations and wait for them to complete
    // TODO
    
  endtask
  
  // setup basic aes features 
  virtual task aes_init();
    bit [31:0] aes_ctrl = '0;    

    // initialize control register
    aes_ctrl[0]   = 0;        // set to encryption
    aes_ctrl[3:1] = 3'b001;   // set to 128b key
    aes_ctrl[4]   = 0;        // start encryption automaticaly
    aes_ctrl[5]   = 0;        // don't overwrite output reg.
    csr_wr(.csr(ral.ctrl), .value(aes_ctrl));       
  endtask

  virtual      task set_mode(bit mode);
    bit [31:0] read_val;

    ral.ctrl.mode.set(mode);
    csr_update(.csr(ral.ctrl));
    
  endtask
  
  virtual task write_key(aes_reg2hw_key_mreg_t [7:0] key);
    csr_wr(.csr(ral.key0), .value(key[0]));
    csr_wr(.csr(ral.key1), .value(key[1]));
    csr_wr(.csr(ral.key2), .value(key[2]));
    csr_wr(.csr(ral.key3), .value(key[3]));
    csr_wr(.csr(ral.key4), .value(key[4]));
    csr_wr(.csr(ral.key5), .value(key[5]));
    csr_wr(.csr(ral.key6), .value(key[6]));
    csr_wr(.csr(ral.key7), .value(key[7]));         
  endtask  

  virtual task add_data(logic [127:0] data);
    `uvm_info(`gfn, $sformatf("\n\t ---| Write data word 0: %02h", data[31:0]), UVM_DEBUG)
    csr_wr(.csr(ral.data_in0), .value(data[31:0]));
    `uvm_info(`gfn, $sformatf("\n\t ---| Write data word 1: %02h", data[63:32]), UVM_DEBUG)
    csr_wr(.csr(ral.data_in1), .value(data[63:32]));
    `uvm_info(`gfn, $sformatf("\n\t ---| Write data word 2: %02h", data[95:64]), UVM_DEBUG)
    csr_wr(.csr(ral.data_in2), .value(data[95:64]));
    `uvm_info(`gfn, $sformatf("\n\t ---| Write data word 0: %02h", data[127:96]), UVM_DEBUG)
    csr_wr(.csr(ral.data_in3), .value(data[127:96]));    
  endtask

  virtual task read_data(output logic [127:0] cypher_txt);
    bit data_rdy = 0;
    bit [31:0] rd_data;
    csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid
    csr_rd(.ptr(ral.data_out3), .value(rd_data));
    cypher_txt[127:96] = rd_data;
    `uvm_info(`gfn, $sformatf("\n\t ---| Read encrypted text from dataout3 %02h", rd_data), UVM_DEBUG)
    csr_rd(.ptr(ral.data_out2), .value(rd_data));
    cypher_txt[95:64] = rd_data;
    `uvm_info(`gfn, $sformatf("\n\t ---| Read encrypted text dataout2 %02h", rd_data), UVM_DEBUG)
    csr_rd(.ptr(ral.data_out1), .value(rd_data));
    cypher_txt[63:32] = rd_data;
    `uvm_info(`gfn, $sformatf("\n\t ---| Read encrypted text dataout1 %02h", rd_data), UVM_DEBUG)
    csr_rd(.ptr(ral.data_out0), .value(rd_data));
    cypher_txt[31:0] = rd_data;
    `uvm_info(`gfn, $sformatf("\n\t ---| Read encrypted text dataout0 %02h", rd_data), UVM_DEBUG)
  endtask
endclass : aes_base_vseq
