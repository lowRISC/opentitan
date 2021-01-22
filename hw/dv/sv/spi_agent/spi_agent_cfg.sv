// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_agent_cfg extends dv_base_agent_cfg;

  // agent cfg knobs
  bit             en_monitor_collect_trans = 1'b1; // enable monitor to collect trans on-the-fly
  bit             en_monitor_checks        = 1'b1; // enable checkers in monitor

  // host mode cfg knobs
  time            sck_period_ps = 50_000; // 20MHz
  bit             sck_polarity;       // aka CPOL
  bit             sck_phase;          // aka CPHA
  bit             host_bit_dir;       // 1 - lsb -> msb, 0 - msb -> lsb
  bit             device_bit_dir;     // 1 - lsb -> msb, 0 - msb -> lsb
  bit             sck_on;             // keep sck on
  // how many bytes monitor samples per transaction
  int             num_bytes_per_trans_in_mon = 4;

  // enable randomly injecting extra delay between 2 sck/word
  bit  en_extra_dly_btw_sck;
  uint min_extra_dly_ns_btw_sck     = 1;
  uint max_extra_dly_ns_btw_sck     = 100;  // small delay to avoid transfer timeout
  uint extra_dly_chance_pc_btw_sck  = 5;    // percentage of extra delay btw each spi clock edge
  // Note: can't handle word delay, if a word is splitted into multiple csb.
  // In that case, control delay in seq level
  bit  en_extra_dly_btw_word;
  uint min_extra_dly_ns_btw_word    = 1;
  uint max_extra_dly_ns_btw_word    = 1000; // no timeout btw word
  uint extra_dly_chance_pc_btw_word = 5;    // percentage of extra delay btw each word

  // interface handle used by driver, monitor & the sequencer
  virtual spi_if  vif;

  `uvm_object_utils_begin(spi_agent_cfg)
    `uvm_field_int (sck_period_ps,    UVM_DEFAULT)
    `uvm_field_int (sck_polarity,     UVM_DEFAULT)
    `uvm_field_int (sck_phase,        UVM_DEFAULT)
    `uvm_field_int (host_bit_dir,     UVM_DEFAULT)
    `uvm_field_int (device_bit_dir,   UVM_DEFAULT)
    `uvm_field_int (en_extra_dly_btw_sck,         UVM_DEFAULT)
    `uvm_field_int (max_extra_dly_ns_btw_sck,     UVM_DEFAULT)
    `uvm_field_int (extra_dly_chance_pc_btw_sck,  UVM_DEFAULT)
    `uvm_field_int (en_extra_dly_btw_word,        UVM_DEFAULT)
    `uvm_field_int (max_extra_dly_ns_btw_word,    UVM_DEFAULT)
    `uvm_field_int (extra_dly_chance_pc_btw_word, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual task wait_sck_edge(sck_edge_type_e sck_edge_type);
    bit [1:0] sck_mode = {sck_polarity, sck_phase};
    bit       wait_posedge;

    // sck polarity   slk_phase       mode
    //            0           0       0: sample at leading podedge  (drive @ prev negedge)
    //            1           0       2: sample at leading negedge  (drive @ prev posedge)
    //            0           1       1: sample at trailing negedge (drive @ curr posedge)
    //            1           1       3: sample at trailing posedge (drive @ curr negedge)
    case (sck_edge_type)
      LeadingEdge: begin
        // wait for leading edge applies to mode 1 and 3 only
        if (sck_mode inside {2'b00, 2'b10}) return;
        if (sck_mode == 2'b01) wait_posedge = 1'b1;
      end
      DrivingEdge:  wait_posedge = (sck_mode inside {2'b01, 2'b10});
      SamplingEdge: wait_posedge = (sck_mode inside {2'b00, 2'b11});
    endcase

    if (wait_posedge) @(posedge vif.sck);
    else              @(negedge vif.sck);
  endtask

endclass
