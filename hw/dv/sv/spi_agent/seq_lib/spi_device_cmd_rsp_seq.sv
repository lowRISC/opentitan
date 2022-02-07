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
  typedef enum {SpiIdle, SpiCmd, SpiData } spi_fsm_e;
  spi_fsm_e spi_state = SpiIdle;

  virtual task body();

    // wait for reset release
    if (cfg.in_reset) wait (!cfg.in_reset);

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
    spi_item item;
    spi_item rsp = spi_item::type_id::create("rsp");
    spi_item rsp_clone;
    spi_cmd_e  cmd;
    bit [31:0] addr;
    bit [31:0] data;
    bit [31:0] addr_cnt = 0;
    int        byte_cnt = 0;

    forever begin
      case (spi_state)
        SpiIdle: begin
          get_nxt_req(item);
          // find start of transaction
          if (item.first_byte) begin
            // decode command
            cmd = cmd_check(item.data.pop_front);
            spi_state = SpiCmd;
          end
        end

        SpiCmd: begin
          get_nxt_req(item);
          // make sure that we did not start a new transaction
          if (item.first_byte) begin
            // decode command
            cmd = cmd_check(item.data.pop_front);
            spi_state = SpiCmd;
            addr_cnt = 0;
          end else begin
            addr[31-8*byte_cnt -: 8] = item.data.pop_front();
            byte_cnt += 1;
            if (byte_cnt+1 == cfg.spi_cmd_width) begin // +1 to accound for the cmd byte
              byte_cnt = 0;
              spi_state = SpiData;
            end
          end
        end

        SpiData: begin
          case (cmd)
            ReadStd, ReadDual, ReadQuad: begin
              // read_until CSB low
              data = $urandom();
              addr_cnt += 4;
              case (cmd)
                ReadStd:  `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp, rsp.data.size() == 8;)
                ReadDual: `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp, rsp.data.size() == 16;)
                default:  `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp, rsp.data.size() == 32;)
              endcase // case (cmd)
              `downcast(rsp_clone, rsp.clone());
              rsp_q.push_back(rsp_clone);
              rsp = new();
              // offload input queue
              get_nxt_req(item);
              if (item.first_byte) begin
                // decode command
                cmd = cmd_check(item.data.pop_front);
                spi_state = SpiCmd;
                addr_cnt = 0;
              end
            end

            WriteStd, WriteDual, WriteQuad: begin
              get_nxt_req(item);
              if (item.first_byte) begin
                // decode command
                cmd = cmd_check(item.data.pop_front);
                spi_state = SpiCmd;
                addr_cnt = 0;
              end else begin
                data[31-8*addr_cnt[1:0] -: 8] = item.data.pop_front();
                addr_cnt += 1;
              end
              // potential TODO add associative array for read back of write data
            end

            default: begin
              `uvm_fatal(`gfn, $sformatf("UNSUPPORTED COMMAND"))
            end
          endcase
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("BAD STATE"))
        end
      endcase
    end
  endtask


  function spi_cmd_e cmd_check(bit[7:0] data);
    spi_cmd_e cmd;
    `downcast(cmd, data, "Illegal Command seen")
    return cmd;
  endfunction
endclass : spi_device_cmd_rsp_seq
