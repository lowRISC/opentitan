// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_env_cfg extends cip_base_env_cfg #(.RAL_T(aes_reg_block));

  `uvm_object_utils_begin(aes_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // Knobs //
  int          data_len_min    = 128;
  int          data_len_max    = 128;
  bit          use_key_mask    = 0;
  bit          use_c_model_pct = 0;


  // rand variables
  rand bit     ref_model;                        // 0: C model 1: OPEN_SSL/BORING_SSL
  rand bit     key_mask;                         // randomly select if we force unused key bits to 0

  // constraints
  constraint c_ref_model { ref_model dist { 0 :/ use_c_model_pct,
                                            1 :/ (100-use_c_model_pct) }; }


  function void post_randomize();
    if(use_key_mask) key_mask = 1;
  endfunction


  virtual function string convert2string();
    string str = "";
    str = super.convert2string();
    str = {str,  $psprintf("\n\t ----| AES ENVIRONMENT CONFIG \t ") };
    str = {str,  $psprintf("\n\t ----| Max data len %d bits \t ", data_len_max) };
    str = {str,  $psprintf("\n\t ----| Min data len %d bits \t ", data_len_min) };
    str = {str,  $psprintf("\n\t ----| Reference model:\t    %s              \t ",
          (ref_model==0) ? "C-MODEL" : "OPEN_SSL" ) };
    str = {str, "\n"};
    return str;
  endfunction


  virtual function void initialize_csr_addr_map_size();
    this.csr_addr_map_size = AES_ADDR_MAP_SIZE;
  endfunction : initialize_csr_addr_map_size

  virtual   function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
  endfunction

endclass
