// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usb20_vseq)

  `uvm_object_new

  usb20_item bp;
  token_pkt tp;
  data_pkt dp;
  handshake_pkt hp;

  virtual task body();
    `uvm_info(`gfn, $sformatf("starting usb20 seq"), UVM_HIGH)
    $display (" Test_Point1 ");

    // JDON: If you look at usbdev_env::connect_phase,
    // your p_sequencer is virtual_sequencer.
    // But your real sequencer is virtual_sequencer.usb20_sequencer_h
    // So you have to use create_item method to set your sequencer.
    // tp = token_pkt::type_id::create("tp");
    `uvm_create_on(tp, p_sequencer.usb20_sequencer_h)
    assert(tp.randomize());
    bp = tp;
    $display (" Test_Point2 ");
    start_item(tp);
    $display (" Test_Point3 ");
    finish_item(tp);
  endtask


endclass
