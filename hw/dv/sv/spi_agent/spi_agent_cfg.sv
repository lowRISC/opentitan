// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_agent_cfg extends dv_base_agent_cfg;

  // enable monitor collection and checker
  bit en_monitor = 1'b1;
  bit en_monitor_checks = 1'b1;

  // byte order (configured by vseq)
  bit byte_order        = 1'b1;

  // host mode cfg knobs
  time sck_period_ps    = 50_000; // 20MHz
  bit host_bit_dir;               // 0 - msb -> lsb, 1 - lsb -> msb
  bit device_bit_dir;             // 0 - msb -> lsb, 1 - lsb -> msb
  bit sck_on;                     // keep sck on
  bit partial_byte;       // Transfering less than byte
  bit [3:0] bits_to_transfer; // Bits to transfer if using less than byte
  bit decode_commands;  // Used in monitor if decoding of commands needed
  bit [2:0] cmd_addr_size = 4; // Address size for command

  //-------------------------
  // spi_host regs
  //-------------------------
  // csid reg
  bit [CSB_WIDTH-1:0] csid;
  // indicate csb is selected in cfg or spi_item
  bit                     csb_sel_in_cfg = 1;
  // configopts register fields
  bit              sck_polarity[NUM_CSB];       // aka CPOL
  bit              sck_phase[NUM_CSB];          // aka CPHA
  bit              full_cyc[NUM_CSB];
  bit [3:0]        csn_lead[NUM_CSB];
  bit [3:0]        csn_trail[NUM_CSB];
  bit [3:0]        csn_idle[NUM_CSB];
  // command register fields
  spi_mode_e       spi_mode;
  // Cmd info configs
  spi_flash_cmd_info cmd_infos[bit[7:0]];
  // Controls address size for flash_cmd_info of type SpiFlashAddrCfg.
  bit              flash_addr_4b_en;

  // If set to null then CSB is high - variable only valid for flash
  spi_item ongoing_flash_cmd;

  // set this mode before starting an item
  spi_func_mode_e  spi_func_mode;

  // address width in bytes (default is 4 bytes)
  int spi_cmd_width   = 4;

  // how many bytes monitor samples per transaction
  int num_bytes_per_trans_in_mon = 4;

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

  // min_idle_ns_after_csb_drop and its max_* sibling specify the range for
  // which CSB will be held inactive at the end of a host sequence item.
  // A value will be randomly chosen in the range. CSB is guaranteed to be inactive for
  // at least min_idle_ns_after_csb_drop before the next transaction begins.
  uint min_idle_ns_after_csb_drop = 1;
  uint max_idle_ns_after_csb_drop = 1000;

  // interface handle used by driver, monitor & the sequencer
  virtual spi_if vif;

  `uvm_object_utils_begin(spi_agent_cfg)
    `uvm_field_int (sck_period_ps,  UVM_DEFAULT)
    `uvm_field_int (host_bit_dir,   UVM_DEFAULT)
    `uvm_field_int (device_bit_dir, UVM_DEFAULT)
    `uvm_field_int (partial_byte,   UVM_DEFAULT)
    `uvm_field_int (decode_commands,    UVM_DEFAULT)
    `uvm_field_int (cmd_addr_size,      UVM_DEFAULT)
    `uvm_field_int (bits_to_transfer,             UVM_DEFAULT)
    `uvm_field_int (en_extra_dly_btw_sck,         UVM_DEFAULT)
    `uvm_field_int (max_extra_dly_ns_btw_sck,     UVM_DEFAULT)
    `uvm_field_int (extra_dly_chance_pc_btw_sck,  UVM_DEFAULT)
    `uvm_field_int (en_extra_dly_btw_word,        UVM_DEFAULT)
    `uvm_field_int (max_extra_dly_ns_btw_word,    UVM_DEFAULT)
    `uvm_field_int (extra_dly_chance_pc_btw_word, UVM_DEFAULT)
    `uvm_field_int (min_idle_ns_after_csb_drop,   UVM_DEFAULT)
    `uvm_field_int (max_idle_ns_after_csb_drop,   UVM_DEFAULT)

    `uvm_field_sarray_int(sck_polarity,   UVM_DEFAULT)
    `uvm_field_sarray_int(sck_phase,      UVM_DEFAULT)
    `uvm_field_sarray_int(full_cyc,        UVM_DEFAULT)
    `uvm_field_sarray_int(csn_lead,        UVM_DEFAULT)
    `uvm_field_sarray_int(csn_trail,       UVM_DEFAULT)
    `uvm_field_sarray_int(csn_idle,        UVM_DEFAULT)
    `uvm_field_enum(spi_mode_e, spi_mode, UVM_DEFAULT)
    `uvm_field_enum(spi_func_mode_e, spi_func_mode, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual task wait_sck_edge(sck_edge_type_e sck_edge_type, bit [CSB_WIDTH-1:0] csb_id);
    bit       wait_posedge;
    bit [1:0] sck_mode = {sck_polarity[csb_id], sck_phase[csb_id]};

    // sck pola   sck_pha   mode
    //        0         0      0: sample at leading  posedge_sck (drive @ prev negedge_sck)
    //        1         0      2: sample at leading  negedge_sck (drive @ prev posedge_sck)
    //        0         1      1: sample at trailing negedge_sck (drive @ curr posedge_sck)
    //        1         1      3: sample at trailing posedge_sck (drive @ curr negedge_sck)
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

    `uvm_info(`gfn, $sformatf("\n  spi_agent_cfg, %s at %s clock, sck_mode %b",
        sck_edge_type.name(), wait_posedge ? "posedge" : "negedge", sck_mode), UVM_DEBUG)
  endtask

  // TODO use  dv_utils_pkg::endian_swap_byte_arr() if possible
  virtual function void swap_byte_order(ref logic [7:0] data[$]);
    bit [7:0] data_arr[];
    data_arr = data;
    `uvm_info(`gfn, $sformatf("\n  spi_agent_cfg, data_q_baseline: %p", data), UVM_DEBUG)
    dv_utils_pkg::endian_swap_byte_arr(data_arr);
    `uvm_info(`gfn, $sformatf("\n  spi_agent_cfg, data_q_swapped:  %p", data_arr), UVM_DEBUG)
    data = data_arr;
  endfunction : swap_byte_order

  virtual function int get_sio_size();
    case (spi_mode)
      Standard: return 1;
      Dual:     return 2;
      Quad:     return 4;
      default:  return 0;
    endcase
  endfunction : get_sio_size

  virtual function void add_cmd_info(spi_flash_cmd_info info);
    // opcode must be unique
    `DV_CHECK_EQ(is_opcode_supported(info.opcode), 0)
    cmd_infos[info.opcode] = info;
  endfunction  : add_cmd_info

  virtual function bit is_opcode_supported(bit [7:0] opcode);
    return cmd_infos.exists(opcode);
  endfunction  : is_opcode_supported

  virtual function void extract_cmd_info_from_opcode(input bit [7:0] opcode,
      output bit [2:0] num_addr_bytes,
      output bit write_command,
      output bit [2:0] num_lanes,
      output int dummy_cycles,
      output int read_pipeline_mode);
    if (cmd_infos.exists(opcode)) begin
      num_addr_bytes     = get_num_addr_byte(opcode);
      write_command      = cmd_infos[opcode].write_command;
      num_lanes          = cmd_infos[opcode].num_lanes;
      dummy_cycles       = cmd_infos[opcode].dummy_cycles;
      read_pipeline_mode = cmd_infos[opcode].read_pipeline_mode;
    end else begin
      // if it's invalid opcode, here is the default setting
      `uvm_info(`gfn, $sformatf("extract invalid opcode: 0x%0h", opcode), UVM_MEDIUM)
      write_command      = 1;
      num_addr_bytes     = 0;
      num_lanes          = 1;
      dummy_cycles       = 0;
      read_pipeline_mode = 0;
    end
  endfunction  : extract_cmd_info_from_opcode

  // this task collects one byte data based on num_lanes, which is used in both monitor and driver
  task read_byte(input int num_lanes,
                 input bit is_device_rsp,
                 input  bit [CSB_WIDTH-1:0] csb_id,
                 output logic [7:0] data);
    int which_bit = 8;
    while (which_bit != 0) begin
      wait_sck_edge(SamplingEdge, csb_id);
      case (num_lanes)
        1: data[--which_bit] = is_device_rsp ? vif.sio[1] : vif.sio[0];
        2: begin
          data[--which_bit] = vif.sio[1];
          data[--which_bit] = vif.sio[0];
        end
        4: begin
          data[--which_bit] = vif.sio[3];
          data[--which_bit] = vif.sio[2];
          data[--which_bit] = vif.sio[1];
          data[--which_bit] = vif.sio[0];
        end
        default: `uvm_fatal(`gfn, $sformatf("Unsupported lanes num 0x%0h", num_lanes))
      endcase
    end

    `uvm_info(`gfn, $sformatf("sampled one byte data for flash: 0x%0h", data), UVM_HIGH)
  endtask

  virtual function int get_num_addr_byte(bit [7:0] opcode);
    `DV_CHECK(cmd_infos.exists(opcode))
    case (cmd_infos[opcode].addr_mode)
      SpiFlashAddrDisabled: return 0;
      SpiFlashAddrCfg: return flash_addr_4b_en ? 4 : 3;
      SpiFlashAddr3b: return 3;
      SpiFlashAddr4b: return 4;
      default: `uvm_fatal(`gfn, "Impossible value")
    endcase
  endfunction  : get_num_addr_byte
endclass : spi_agent_cfg
