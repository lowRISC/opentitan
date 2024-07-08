// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_item extends uvm_sequence_item;

  // Stimulus ID (incremented when generating stimulus transactions, not used for checking but
  // very useful for debug/development)
  int                      stim_id;
  // Transfer ID
  int                      tran_id;

  // Model the state of an in-progress i2c transfer. This can be used as a cheap proxy for
  // breaking up the transfer into smaller sequence items (bytes, bits, etc.) when we need to
  // update our predictions mid-transfer.
  transfer_state_e         state;

  // Address / Direction
  bit [9:0]                addr; // enough to support both 7 & 10-bit target address
  rw_e                     dir; // Transfer direction bit
  bus_op_e                 bus_op;
  i2c_pkg::acknack_e       addr_ack; // ACK-bit for addr+dir byte

  // Transaction data part
  int                      num_data; // Number of valid data bytes (== data_q.size())
  bit [7:0]                data_q[$]; // Queue of data bytes in the transfer
  bit                      data_ack_q[$]; // Holds the corresponding ack/nack for data_q bytes

  // Transaction control part
  // Control flags used to model the state of ongoing transfers
  bit                      rstart_front; // Transfer started with an RSTART
  bit                      rstart_back; // Transfer ended with an RSTART
  //
  // DUT-Controller
  // Control Flags (mirroring the FMTFIFO interface flags)
  rand bit [7:0]           fbyte;
  rand bit                 nakok, rcont, read, stop, start;

  //
  // DUT-Target
  i2c_acq_byte_id_e        signal; // ACQDATA.SIGNAL

  // The following fields are used when using the seq_item to create transactions byte-by-byte in
  // the i2c_agent. Used when interacting with the i2c_driver and 'drv_type' to create stimulus.
  // TODO: Remove / Refactor to use bus_op + data_q instead
  logic [7:0]              wdata;
  logic [7:0]              rdata;
  // This field is used by the i2c_driver to control the driving behaviour for a single sequence
  // item. This is not a great abstraction, hopefully one day it can be removed as part of a larger
  // refactor.
  // Also see #14825
  drv_type_e               drv_type;

  // Use for debug print
  string                   pname = "";

  // Use to indicate the number of cycles Agent consumes for Write data or while in idle state
  int                      wait_cycles = 8;

  constraint fbyte_c     { fbyte      inside {[0 : 127] }; }
  constraint rcont_c     {
     solve read, stop before rcont;
     // for read request, rcont and stop must be complementary set
     if (read) {
       rcont == ~stop;
     } else {
       rcont dist { 1 :/ 1, 0 :/ 2 };
     }
  }

  constraint wait_cycles_c {
    wait_cycles == 8;
  }

  // In the I2C block-level DV environment, we only use the .compare() method for DUT-Controller
  // transactions. DUT-Target transactions use checking routines which explicitly only compare a
  // different subset of the fields. Hence, the NOCOMPARE attributes only apply to DUT-Controller
  // transaction comparison.
  //
  `uvm_object_utils_begin(i2c_item)
    `uvm_field_int(stim_id,                       UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(tran_id,                       UVM_DEFAULT | UVM_DEC)
    `uvm_field_enum(transfer_state_e, state,      UVM_DEFAULT               | UVM_NOCOMPARE)
    `uvm_field_enum(bus_op_e, bus_op,             UVM_DEFAULT)
    `uvm_field_int(addr,                          UVM_DEFAULT)
    `uvm_field_enum(i2c_pkg::rw_e, dir,           UVM_DEFAULT | UVM_NOPRINT)
    `uvm_field_enum(i2c_pkg::acknack_e, addr_ack, UVM_DEFAULT)
    `uvm_field_int(num_data,                      UVM_DEFAULT | UVM_NOPRINT)
    `uvm_field_queue_int(data_q,                  UVM_DEFAULT | UVM_NOPRINT)
    `uvm_field_queue_int(data_ack_q,              UVM_DEFAULT | UVM_NOPRINT)
    `uvm_field_int(start,                         UVM_DEFAULT)
    `uvm_field_int(rstart_front,                  UVM_DEFAULT)
    `uvm_field_int(rstart_back,                   UVM_DEFAULT)
    `uvm_field_int(stop,                          UVM_DEFAULT)
    // acqfifo fields
    `uvm_field_enum(i2c_acq_byte_id_e, signal,    UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    // fmtfifo fields
    `uvm_field_int(fbyte,                         UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(read,                          UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(rcont,                         UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(nakok,                         UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    // +start
    // +stop

    `uvm_field_int(wait_cycles,                   UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    // #TODO remove : i2c_driver fields
    `uvm_field_int(wdata,                         UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(rdata,                         UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_enum(drv_type_e,  drv_type,        UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction

  // Clear all data fields in the item (without clearing any control conditions, which is
  // handled seperately in clear_flags()).
  //
  function void clear_data();
    num_data = 0;
    addr     = 0;
    drv_type = None;
    data_q.delete();
    wdata = 0;
    rdata = 0;
    addr_ack = i2c_pkg::NACK;
    data_ack_q.delete();
  endfunction : clear_data

  // Clear all control symbol fields.
  //
  function void clear_flags();
    start        = 1'b0;
    stop         = 1'b0;
    read         = 1'b0;
    rcont        = 1'b0;
    nakok        = 1'b0;
    rstart_front = 1'b0;
    rstart_back  = 1'b0;
  endfunction : clear_flags

  // Clear all data and control symbol fields (without re-constructing the item).
  //
  function void clear_all();
    clear_data();
    clear_flags();
  endfunction : clear_all

  virtual function string convert2string();
    string str = "";
    str = {str, $sformatf("%s:tran_id      = %0d\n", pname, tran_id)};
    str = {str, $sformatf("%s:bus_op       = %s\n",    pname, bus_op.name)};
    str = {str, $sformatf("%s:addr         = 0x%2x\n", pname, addr)};
    str = {str, $sformatf("%s:num_data     = %0d\n", pname, num_data)};
    str = {str, $sformatf("%s:start        = %1b\n", pname, start)};
    str = {str, $sformatf("%s:stop         = %1b\n", pname, stop)};
    str = {str, $sformatf("%s:read         = %1b\n", pname, read)};
    str = {str, $sformatf("%s:rstart_front = %1b\n", pname, rstart_front)};
    str = {str, $sformatf("%s:rstart_back  = %1b\n", pname, rstart_back)};
    foreach (data_q[i]) begin
      str = {str, $sformatf("%s:data_q[%0d]=0x%2x\n", pname, i, data_q[i])};
    end
    return str;
  endfunction

  // Custom printer for the data rows (data + ACK/NACK)
  function void do_print(uvm_printer printer);
    super.do_print(printer);

    printer.print_field_int("num_data", num_data, 32, UVM_DEC);
    foreach (data_q[i]) begin
      i2c_pkg::acknack_e acknack = i2c_pkg::acknack_e'(data_ack_q[i]);
      printer.print_generic(
        .name($sformatf("data_q[%0d]", i)),
        .type_name("-"),
        .size(9),
        .value($sformatf("8'h%2x %0s",
                         data_q[i],
                         acknack.name()))
      );
    end

  endfunction

endclass : i2c_item
