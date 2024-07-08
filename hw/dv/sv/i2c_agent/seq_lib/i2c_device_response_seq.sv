// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Agent-Target sequence which accepts all write-transfer data and returns it in read-transfers.
// aka. 'autoresponder'
// - Write transfers to any address are accepted, and data is stored in a queue such that response
//   data to reads is returned in the same order it was written to that address.
//
class i2c_device_response_seq extends i2c_base_seq;

  ///////////////
  // VARIABLES //
  ///////////////

  typedef bit [7:0] data_q[$];

  // Only 7-bit addresses are supported
  data_q response_mem[2**Addr7BitMode]; // One queue per 7-bit address.

  `uvm_object_utils(i2c_device_response_seq)
  `uvm_object_new

  /////////////
  // METHODS //
  /////////////


  virtual task body();
    fork
      // The base_seq body behaviour for Target operations captures in-progress transfers from
      // the monitor, then calls a number of hooks methods where we may wish to drive traffic or
      // capture data. For this sequence, we just need to override the hooks to achieve the
      // intended autoresponder function.
      super.body();
      // Spawn some background processes that run the entire length of the sequence
      fork
        // This task clears out the response memory upon each reset assertion
        forever begin
          @(negedge cfg.vif.rst_ni);
          foreach (response_mem[i]) response_mem[i].delete();
        end
        // The cfg field 'got_stop' is used in block-level DV to prevent new stimulus from being
        // generated before the previous transaction has completed. When used at chip-level, when
        // the block-level sequences are not running, we need to handle this field differently.
        // Simply clear this field here whenever it is set.
        // TODO(#) Remove this hacky-hack, hopefully along with the cfg.got_stop field altogether.
        forever begin
          wait(cfg.got_stop == 1);
          cfg.got_stop = 0;
        end
      join_none
    join
  endtask : body


  // We don't need to hook the address-byte ACK here (drive_addr_byte_ack()), as the base class
  // will ACK to accept all transfers by default, which matches the behaviour we want for this
  // sequence.


  // This method hooks the end of every data byte in an in-progress WRITE transfer.
  // Store the data byte into the local memory, for recall by the next read operation.
  virtual task drive_write_byte_ack();
    bit[Addr7BitMode-1:0] xfer_addr = inp_xfer.addr[Addr7BitMode-1:0];

    response_mem[xfer_addr].push_back(inp_xfer.data_q[$]);
    `uvm_info(`gfn, $sformatf(
      "Autoresponder sequence storing the following write : addr:8'h%2x byte:8'h%2x",
      xfer_addr, inp_xfer.data_q[$]), UVM_DEBUG)

    // Drive the ACK to this write byte.
    // This sequence will always ACK all write bytes.
    super.drive_write_byte_ack();
  endtask : drive_write_byte_ack


  // This method hooks the start of every data byte in an inprogress READ transfer.
  // Fetch any read data from the local memory, and drive the data byte with this value.
  virtual task drive_read_byte();
    bit[Addr7BitMode-1:0] xfer_addr = inp_xfer.addr[Addr7BitMode-1:0];
    bit [7:0]             rdata;

    if (response_mem[xfer_addr].size() == 0) begin
      // We haven't previously seen a write transfer at this address. There is no data to return.
      `uvm_fatal(`gfn, $sformatf("Read requested, but write-queue at this address is empty!"))
    end

    // Fetch the data written to this address, and use it to populate the drive item.
    rdata = response_mem[xfer_addr].pop_front();

    `uvm_info(`gfn, $sformatf(
      "Autoresponder sequence transmitting based byte based on read : addr:8'h%2x byte:8'h%2x",
      xfer_addr, rdata), UVM_DEBUG)

    // Drive the data byte
    `uvm_create_obj(REQ, req);
    start_item(req);
    req.drv_type = RdData;
    req.rdata = rdata;
    finish_item(req);
  endtask : drive_read_byte


endclass : i2c_device_response_seq
