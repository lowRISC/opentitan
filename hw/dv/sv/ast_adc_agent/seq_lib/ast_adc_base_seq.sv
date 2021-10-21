// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ast_adc_base_seq extends dv_base_seq #(
    .REQ         (ast_adc_item),
    .CFG_T       (ast_adc_agent_cfg),
    .SEQUENCER_T (ast_adc_sequencer)
  );

  // ADC agent sequences
  // Send a random sample to each ADC channel and wait for responses
  ast_adc_all_random_seq  m_ast_adc_all_random_seq;
  // Send ramps with random steps to each ADC channel
  ast_adc_random_ramp_seq m_adc_random_ramp_seq;

  `uvm_object_utils(ast_adc_base_seq)

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
