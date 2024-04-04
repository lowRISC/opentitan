// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// put these covergoups outside the class in order to create them anywhere after get cfg object
// if more than one interrupt/alert registers, these can be reused
// in extended cov class, better to have the covergroup inside the class and create in new function
covergroup intr_cg (uint num_interrupts) with function sample(uint intr,
                                                              bit intr_en,
                                                              bit intr_state);
  cp_intr: coverpoint intr {
    bins all_values[] = {[0:num_interrupts-1]};
  }
  cp_intr_en: coverpoint intr_en;
  cp_intr_state: coverpoint intr_state;
  cross cp_intr, cp_intr_en, cp_intr_state;
endgroup

covergroup intr_test_cg (uint num_interrupts) with function sample(uint intr,
                                                                   bit intr_test,
                                                                   bit intr_en,
                                                                   bit intr_state);
  cp_intr: coverpoint intr {
    bins all_values[] = {[0:num_interrupts-1]};
  }
  cp_intr_test: coverpoint intr_test;
  cp_intr_en: coverpoint intr_en;
  cp_intr_state: coverpoint intr_state;
  cross cp_intr, cp_intr_test, cp_intr_en, cp_intr_state {
    illegal_bins test_1_state_0 = binsof(cp_intr_test) intersect {1} &&
                                  binsof(cp_intr_state) intersect {0};
  }
endgroup

covergroup intr_pins_cg (uint num_interrupts) with function sample(uint intr_pin,
                                                                   bit  intr_pin_value);
  cp_intr_pin: coverpoint intr_pin {
    bins all_pins[] = {[0:num_interrupts-1]};
  }
  cp_intr_pin_value: coverpoint intr_pin_value {
    bins values[] = {0, 1};
    bins transitions[] = (0 => 1), (1 => 0);
  }
  cp_intr_pins_all_values: cross cp_intr_pin, cp_intr_pin_value;
endgroup

// This covergroup sampled at changing edges of both clocks.
covergroup resets_cg (string name) with function sample(logic [1:0] resets);
  option.per_instance = 1;
  option.name = name;

  resets_trans: coverpoint resets {
  // This coverpoint collects the toggle coverage as below:
  //          _ _ _         _ _ _
  // RESET1        |_ _ _ _|
  //          _ _ _ _         _ _ _ _
  // RESET0          |_ _ _ _|
    bins rst1_start_first_end_first = ('b01 => 'b00 => 'b10 => 'b11);

  // This coverpoint collects the toggle coverage as below:
  //          _ _ _         _ _ _ _ _
  // RESET1        |_ _ _ _|
  //          _ _         _ _ _ _ _
  // RESET0      |_ _ _ _|
    bins rst1_start_last_end_last = ('b10 => 'b00 => 'b01 => 'b11);

  // This coverpoint collects the toggle coverage as below:
  //          _ _ _         _ _ _ _ _
  // RESET1        |_ _ _ _|
  //          _ _ _ _     _ _ _ _ _
  // RESET0          |_ _|
    bins rst1_start_first_end_last = ('b01 => 'b00 => 'b01 => 'b11);

  // This coverpoint collects the toggle coverage as below:
  //          _ _ _ _     _ _ _ _ _
  // RESET1          |_ _|
  //          _ _ _         _ _ _ _ _
  // RESET0        |_ _ _ _|
    bins rst1_start_last_end_first = ('b10 => 'b00 => 'b10 => 'b11);
  }
endgroup

class tl_errors_cg_wrap;
  // This covergroup sampled all kinds of TL error cases.
  covergroup tl_errors_cg (string name)
      with function sample(bit unmapped_err,
                           bit csr_size_err,
                           bit mem_byte_access_err,
                           bit mem_wo_err,
                           bit mem_ro_err,
                           bit tl_protocol_err,
                           bit write_w_instr_type_err,
                           bit instr_type_err);
    option.per_instance = 1;
    option.name = name;

    // these cp should be disabled (set weight to 0), when they're not applicable for the block
    cp_unmapped_err: coverpoint unmapped_err;
    cp_csr_size_err: coverpoint csr_size_err;
    cp_mem_byte_access_err: coverpoint mem_byte_access_err;
    cp_mem_wo_err: coverpoint mem_wo_err;
    cp_mem_ro_err: coverpoint mem_ro_err;

    // we don't enumerate the various kinds of TL protocol errors here because there is a covergroup
    // in tl_agent, which covers those
    // No need to cover the case of 0, as protocol error may be the only error and 0 never happens.
    cp_tl_protocol_err: coverpoint tl_protocol_err {
      bins covered = {1};
    }

    cp_write_w_instr_type_err: coverpoint write_w_instr_type_err;
    cp_instr_type_err: coverpoint instr_type_err;
  endgroup

  // Function: new
  function new(string name);
    tl_errors_cg = new(name);
  endfunction : new

  // Function: sample
  function void sample(bit unmapped_err,
                       bit csr_size_err,
                       bit mem_byte_access_err,
                       bit mem_wo_err,
                       bit mem_ro_err,
                       bit tl_protocol_err,
                       bit write_w_instr_type_err,
                       bit instr_type_err);
    tl_errors_cg.sample(unmapped_err, csr_size_err, mem_byte_access_err, mem_wo_err,
                        mem_ro_err, tl_protocol_err, write_w_instr_type_err, instr_type_err);
  endfunction : sample

endclass

class tl_intg_err_cg_wrap;
  // This covergroup sampled all kinds of TL integrity error and numbers of error bits.
  covergroup tl_intg_err_cg (string name) with function sample(tl_intg_err_e tl_intg_err_type,
                                                                   uint          num_cmd_err_bits,
                                                                   uint          num_data_err_bits,
                                                                   bit           is_mem);
    option.per_instance = 1;
    option.name = name;

    cp_tl_intg_err_type: coverpoint tl_intg_err_type;

    cp_num_cmd_err_bits: coverpoint num_cmd_err_bits {
      bins values[] = {[0:MAX_TL_ECC_ERRORS]};
    }
    cp_num_data_err_bits: coverpoint num_data_err_bits {
      bins values[] = {[0:MAX_TL_ECC_ERRORS]};
    }
    cp_is_mem: coverpoint is_mem;
  endgroup

  // Function: new
  function new(string name);
    tl_intg_err_cg = new(name);
  endfunction : new

  // Function: sample
  function void sample(tl_intg_err_e tl_intg_err_type,
                       uint          num_cmd_err_bits,
                       uint          num_data_err_bits,
                       bit           is_mem);
    tl_intg_err_cg.sample(tl_intg_err_type, num_cmd_err_bits, num_data_err_bits, is_mem);
  endfunction : sample
endclass

class tl_intg_err_mem_subword_cg_wrap;
  // Design handles mem subword write specially. Add this CG to cover all types subword write
  // with integrity errors
  covergroup tl_intg_err_mem_subword_cg (string name) with function sample(
        tl_intg_err_e tl_intg_err_type,
        bit            write,
        int            num_enable_bytes);
    option.per_instance = 1;
    option.name = name;

    cp_tl_intg_err_type: coverpoint tl_intg_err_type;

    cp_num_num_enable_bytes: coverpoint num_enable_bytes {
      bins full_word = {BUS_DW / 8};
      bins partial   = {[0 : BUS_DW / 8 - 1]};
    }
    cp_write: coverpoint write;

    cr_all: cross cp_tl_intg_err_type, cp_num_num_enable_bytes, cp_write;
  endgroup

  // Function: new
  function new(string name);
    tl_intg_err_mem_subword_cg = new(name);
  endfunction : new

  // Function: sample
  function void sample(tl_intg_err_e tl_intg_err_type,
                       uint          write,
                       uint          num_enable_bytes);
    tl_intg_err_mem_subword_cg.sample(tl_intg_err_type, write, num_enable_bytes);
  endfunction : sample
endclass

class cip_base_env_cov #(type CFG_T = cip_base_env_cfg) extends dv_base_env_cov #(CFG_T);
  `uvm_component_param_utils(cip_base_env_cov #(CFG_T))

  intr_cg        intr_cg;
  intr_test_cg   intr_test_cg;
  intr_pins_cg   intr_pins_cg;
  resets_cg      resets_cg;
  // Coverage for sticky interrupt functionality described in CIP specification
  // As some interrupts are non-sticky, this covergroup should be populated on "as and when needed"
  // basis in extended <ip>_env_cov class for interrupt types that are sticky
  bit_toggle_cg_wrap sticky_intr_cov[string];

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.num_interrupts != 0) begin
      intr_cg      = new(cfg.num_interrupts);
      intr_test_cg = new(cfg.num_interrupts);
      intr_pins_cg = new(cfg.num_interrupts);
    end
    if (cfg.num_edn) resets_cg = new("dut_and_edn_rsts");
  endfunction

endclass
