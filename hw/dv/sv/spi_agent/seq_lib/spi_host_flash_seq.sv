// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_flash_seq extends spi_base_seq;

  rand bit [7:0] opcode;
  // if address isn't provided, will be randomized based on cmd_infos
  rand bit [7:0] address_q[$];
  rand bit [7:0] payload_q[$];
  rand int       read_size;

  bit [CSB_WIDTH-1:0] csb_sel = 0;

  `uvm_object_utils_begin(spi_host_flash_seq)
    `uvm_field_int(opcode,          UVM_DEFAULT)
    `uvm_field_int(read_size,       UVM_DEFAULT)
    `uvm_field_queue_int(payload_q, UVM_DEFAULT)
    `uvm_field_queue_int(address_q, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  virtual task body();
    int num_addr_bytes, num_lanes, dummy_cycles, read_pipeline_mode;
    bit write_command;

    req = spi_item::type_id::create("req");
    start_item(req);

    cfg.spi_func_mode = SpiModeFlash;
    cfg.extract_cmd_info_from_opcode(opcode,
        // output
        num_addr_bytes, write_command, num_lanes, dummy_cycles, read_pipeline_mode);
    if (address_q.size() == 0) begin
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(address_q,
          address_q.size == num_addr_bytes;)
    end else begin
      `DV_CHECK_EQ(address_q.size(), num_addr_bytes)
    end

    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   item_type == SpiTransNormal;
                                   csb_sel == local::csb_sel;
                                   opcode == local::opcode;
                                   write_command == local::write_command;
                                   num_lanes == local::num_lanes;
                                   dummy_cycles == local::dummy_cycles;
                                   read_pipeline_mode == local::read_pipeline_mode;
                                   address_q.size() == num_addr_bytes;
                                   foreach (address_q[i]) {
                                     address_q[i] == local::address_q[i];
                                   }
                                   if (num_lanes == 0) {
                                    read_size == 0;
                                    payload_q.size() == 0;
                                   } else {
                                    if (write_command) {
                                      read_size == 0;
                                      payload_q.size() == local::payload_q.size();
                                      foreach (payload_q[i]) {
                                        payload_q[i] == local::payload_q[i];
                                      }
                                    } else { // read
                                      read_size == local::read_size;
                                      payload_q.size() == 0;
                                    }
                                   }
                                  // TODO, consolidate data and payload later
                                  data.size == 0;)
    finish_item(req);
    get_response(rsp);
  endtask

endclass
