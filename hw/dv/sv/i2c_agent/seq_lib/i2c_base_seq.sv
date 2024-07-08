// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This base_vseq contains common subroutines for the agent to drive stimulus as either an
// I2C-Controller (bus-initiator, or 'Host' in wider OpenTitan verbiage) or as an I2C-Target
// (bus-receiver, or OpenTitan 'Device').
//
// - (cfg.if_mode == Device) As an I2C-Target, the default behaviour is to operate in a
//   reactive-agent mode, awaiting the monitor to report observations via the
//   TLM 'p_sequencer.in_progress_ports', and passing items to the driver based on this.
// - (cfg.if_mode == Host) #FIXME - This configuration appears unused.
//
class i2c_base_seq extends dv_base_seq #(
    .REQ         (i2c_item),
    .CFG_T       (i2c_agent_cfg),
    .SEQUENCER_T (i2c_sequencer)
  );

  ///////////////
  // VARIABLES //
  ///////////////

  // Store a handle to the in-progress transfer item captured by the monitor.
  i2c_item inp_xfer;

  // This queue stores a sequence of items to be passed to the driver for stimulus creation.
  // Typically, this variable is populated by the entity that creates the sequence before starting
  // it. It is also possible to push_back() new items piecemeal while the sequence is running.
  REQ req_q[$];

  // Set this bit via. seq_stop() to immediately halt the sequence.
  protected bit stop;

  `uvm_object_utils(i2c_base_seq)
  `uvm_object_new

  ////////////////////////////////////
  // RANDOM VARIABLES & CONSTRAINTS //
  ////////////////////////////////////

  // Random data, used as payload data for Agent-Controller transactions (if_mode == Host).
  rand bit [7:0] data_q[$];
  // Constrain the number of bytes of payload data
  constraint data_q_size_c {
    data_q.size() inside {[cfg.i2c_host_min_data_rw : cfg.i2c_host_max_data_rw]};
  }

  /////////////
  // METHODS //
  /////////////


  virtual task body();
    case (cfg.if_mode)
      Device: while (!stop) begin // Agent-Target
        // Get reactive agent items from the i2c_monitor, and use them to monitor the in-progress
        // transaction and to drive the bus accordingly.
        inp_xfer = null;
        get_in_progress_transfer_item(inp_xfer, p_sequencer.target_mode_in_progress_fifo);
        if (inp_xfer != null) begin
          `uvm_info(`gfn, $sformatf("i2c_agent_seq: got new in-progress transfer item :\n%s",
                                    inp_xfer.sprint()), UVM_DEBUG)
          fork begin : iso_fork
            fork
              forever print_inp_xfer_state_changes();
              send_device_mode_txn();
            join_any
            disable fork;
          end : iso_fork join
        end
      end
      Host: begin // Agent-Controller
        send_host_mode_txn(); // (NOTE. Unused)
      end
      default: `uvm_fatal(`gfn, "Shouldn't get here!")
    endcase
  endtask : body


  // This task awaits a new item from the i2c_monitor to arrive in the corresponding TLM fifo.
  //
  virtual task get_in_progress_transfer_item(output i2c_item inp_xfer,
                                             input i2c_analysis_fifo fifo);
    fork begin: iso_fork
      fork
        // Block until a new item arrives from the monitor
        begin
          i2c_item item;
          fifo.get(item);
          `downcast(inp_xfer, item)
        end
        // If seq_stop() is called, break out of the above wait-state immediately.
        wait (stop);
      join_any
      #0;
      disable fork;
    end: iso_fork join
  endtask : get_in_progress_transfer_item


  virtual task print_inp_xfer_state_changes();
    @(inp_xfer.state);
    `uvm_info(`gfn, $sformatf("inp_xfer.state moved to %0s.", inp_xfer.state.name()), UVM_DEBUG)
  endtask : print_inp_xfer_state_changes


  // As an Agent-Target, drive the bus based on the reactive-agent item passed from the i2c_monitor
  //
  virtual task send_device_mode_txn();

    while (!(inp_xfer.state inside {StStopped, StAborted})) begin

      @(inp_xfer.state);
      case (inp_xfer.state)
        StAddrByteRcvd: begin
          // Drive an ACK/NACK to the address byte
          drive_addr_byte_ack();
        end
        StDataByte: begin
          if (inp_xfer.dir == i2c_pkg::READ) begin
            // The agent drives the read bytes as target-transmitter.
            drive_read_byte();
          end
        end
        StDataByteRcvd: begin
          if (inp_xfer.dir == i2c_pkg::WRITE) begin
            // The agent now needs to ACK or NACK the received write data byte.
            drive_write_byte_ack();
          end
        end
        default:; // We want to fall through for all other states.
      endcase

    end // while(!stopped)

    `uvm_info(`gfn, "Got to end of Agent-Target transfer. Now awaiting new transfer.", UVM_DEBUG)
  endtask : send_device_mode_txn


  virtual task drive_addr_byte_ack();
    `uvm_create_obj(REQ, req);
    start_item(req);
    req.drv_type = DevAck;
    finish_item(req);
    `uvm_info(`gfn, "drive_addr_byte_ack()::finish_item()", UVM_DEBUG)
  endtask : drive_addr_byte_ack


  virtual task drive_read_byte();
    `uvm_create_obj(REQ, req);
    start_item(req);
    req.drv_type = RdData;
    req.rdata = $urandom;
    finish_item(req);
    `uvm_info(`gfn, "drive_read_byte()::finish_item()", UVM_DEBUG)
  endtask : drive_read_byte


  virtual task drive_write_byte_ack();
    `uvm_create_obj(REQ, req);
    start_item(req);
    req.drv_type = DevAck;
    finish_item(req);
    `uvm_info(`gfn, "drive_write_byte_ack()::finish_item()", UVM_DEBUG)
  endtask : drive_write_byte_ack


  // As an Agent-Controller, drive the bus with a single randomized seq_item
  // - Use data from the class randomized variable 'data_q[$]'
  //
  virtual task send_host_mode_txn();
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
      data_q.size() == local::data_q.size();
      foreach (data_q[i]) {
        data_q[i] == local::data_q[i];
      }
    )
    finish_item(req);
    get_response(rsp);
  endtask : send_host_mode_txn


  // This routine can be called to gracefully end the sequence immediately
  //
  virtual task seq_stop();
    stop = 1'b1;
    wait_for_sequence_state(UVM_FINISHED);
  endtask : seq_stop


  // Override the uvm print implementation to only show the '.drv_type' and any associated data
  // of each item in the 'req_q'.
  //
  virtual function void do_print(uvm_printer printer);
    super.do_print(printer);
    foreach (req_q[i]) begin
      printer.print_string($sformatf("req_q[%0d].drv_type", i), req_q[i].drv_type.name());
      if (req_q[i].drv_type == RdData) begin
        printer.print_field("  rdata", req_q[i].rdata, 8);
      end
    end
  endfunction: do_print


endclass : i2c_base_seq
