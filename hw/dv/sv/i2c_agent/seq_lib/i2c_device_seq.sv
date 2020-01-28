// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_device_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_device_seq)

  `uvm_object_new

  rand int dly_to_send_nack;
  rand int dly_to_send_ack;
  rand int dly_to_send_stop;
  rand int dly_to_send_data;

  constraint dly_to_send_ack_c     { dly_to_send_ack   inside {[0:cfg.max_delay_ack]}; }
  constraint dly_to_send_nack_c    { dly_to_send_nack  inside {[0:cfg.max_delay_nack]}; }
  constraint dly_to_send_stop_c    { dly_to_send_stop  inside {[0:cfg.max_delay_stop]}; }
  constraint dly_to_send_rd_data_c { dly_to_send_data  inside {[0:cfg.max_delay_data]}; }

  task body();
    req = i2c_item::type_id::create("req");
    start_item(req);
    // randomize item
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        dly_to_send_nack == local::dly_to_send_nack;
        dly_to_send_ack  == local::dly_to_send_ack;
        dly_to_send_stop == local::dly_to_send_stop;
        dly_to_send_data == local::dly_to_send_data;
        )
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "i2c device rsp done", UVM_HIGH)
  endtask : body

endclass : i2c_device_seq
