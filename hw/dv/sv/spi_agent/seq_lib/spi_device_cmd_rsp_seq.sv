// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// --------------------
// Device sequence
// This sequence acts as the device
// with a DUT that acts as host.
// the sequence will poll for read and write commands
// for read commands it will sendback random data
// --------------------


class spi_device_cmd_rsp_seq extends spi_device_seq;
  `uvm_object_utils(spi_device_cmd_rsp_seq)
  `uvm_object_new

  // read queue
  spi_item rsp_q[$];
  spi_fsm_e spi_state = SpiIdle;

  // state-variables
  spi_cmd_e  cmd;
  int        byte_cnt = 0;

  virtual task body();

    // wait for reset release
    if (cfg.in_reset) wait(!cfg.in_reset);

    fork
      // get transactions from host
      get_req();
      // decode transactions
      decode_cmd();
      // transmit response
      send_rsp(rsp_q);
    join
  endtask : body


  virtual task decode_cmd();
    spi_item         item;

    forever begin

      // Block here until the monitor sends a new seq_item, or we end the transaction.
      fork begin: iso_fork
        fork
          get_nxt_req(item);
          begin
            // If CSB goes inactive, cleanup then go back to waiting for the next txn
            @(posedge cfg.vif.csb[0]);
            spi_state = SpiIdle;
            rsp_q.delete();
          end
        join_any
        disable fork;
      end: iso_fork join
      if (cfg.vif.csb[0] == 1'b1) continue;

      // Check for start of transaction.
      if (item.first_byte) begin
        // decode command, check for errors
        cmd = cmd_check(item.data.pop_front);
        spi_state = SpiCmd;
      end

      case (spi_state)
        SpiIdle:;
        SpiCmd: begin
          byte_cnt += 1;
          if (byte_cnt == cfg.spi_cmd_width) begin
            byte_cnt  = 0;
            spi_state = SpiData;
            // If the command is a READ, we need to begin sending data now.
            if (cmd inside {ReadStd, ReadDual, ReadQuad}) handle_reads();
          end
        end
        SpiData: begin
          case (cmd)
            ReadStd,  ReadDual,  ReadQuad: handle_reads();
            WriteStd, WriteDual, WriteQuad: handle_writes(item);
            default: `uvm_fatal(`gfn, $sformatf("UNSUPPORTED COMMAND"))
          endcase
        end
        default: `uvm_fatal(`gfn, $sformatf("BAD STATE"))
      endcase // (spi_state)

    end // forever

  endtask : decode_cmd

  function void handle_reads();
    spi_item rsp = spi_item::type_id::create("rsp");
    spi_item rsp_clone;

    case (cmd)
      ReadStd :  cfg.spi_mode = Standard;
      ReadDual:  cfg.spi_mode = Dual;
      ReadQuad:  cfg.spi_mode = Quad;
      default :  cfg.spi_mode = RsvdSpd;
    endcase

    // Create rsp
    // Currently, the rsp is just random data
    rsp = new();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp,
      (cmd == ReadStd)  -> data.size() ==  256;
      (cmd == ReadDual) -> data.size() ==  512;
      (cmd == ReadQuad) -> data.size() == 1024;
      num_lanes == cfg.get_sio_size();)
    `downcast(rsp_clone, rsp.clone());
    rsp_q.push_back(rsp_clone);

  endfunction : handle_reads

  function void handle_writes(spi_item item);
    void'(item.data.pop_front());
    // potential TODO add associative array for read back of write data
  endfunction : handle_writes

  function spi_cmd_e cmd_check(bit [7:0] data);
    spi_cmd_e cmd;
    `downcast(cmd, data, "Illegal Command seen")
    return cmd;
  endfunction : cmd_check
endclass : spi_device_cmd_rsp_seq
