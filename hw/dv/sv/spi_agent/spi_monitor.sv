// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_monitor extends dv_base_monitor#(
    .ITEM_T (spi_item),
    .CFG_T  (spi_agent_cfg),
    .COV_T  (spi_agent_cov)
  );
  `uvm_component_utils(spi_monitor)

  spi_item host_item, host_clone;
  spi_item device_item, device_clone;
  spi_cmd_e cmd;
  spi_cmd_e cmdtmp;
  int cmd_byte;

  // Analysis port for the collected transfer.
  uvm_analysis_port #(spi_item) host_analysis_port;
  uvm_analysis_port #(spi_item) device_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_analysis_port   = new("host_analysis_port", this);
    device_analysis_port = new("device_analysis_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    collect_trans(phase);
  endtask

  // collect transactions forever
  virtual protected task collect_trans(uvm_phase phase);
    host_item   = spi_item::type_id::create("host_item", this);
    device_item = spi_item::type_id::create("device_item", this);

    forever begin
      @(negedge cfg.vif.csb);
      // indicate that this the first byte in a spi transaction
      host_item.first_byte = 1;
      cmd = CmdOnly;
      cmd_byte = 0;
      if (cfg.is_flash_mode == 0) begin
        collect_curr_trans();
      end else begin
        collect_flash_trans();
      end
    end
  endtask : collect_trans

  virtual protected task collect_curr_trans();
    fork
      begin: isolation_thread
        fork
          begin: csb_deassert_thread
            wait(cfg.vif.csb[cfg.csb_sel] == 1'b1);
          end
          begin: sample_thread
            // for mode 1 and 3, get the leading edges out of the way
            cfg.wait_sck_edge(LeadingEdge);
            forever begin
              bit [7:0] host_byte;    // from sio
              bit [7:0] device_byte;  // from sio
              int       which_bit_h;
              int       which_bit_d;
              int       data_shift;
              bit [3:0] num_samples;
              if (cfg.partial_byte == 1) begin
                num_samples = cfg.bits_to_transfer;
              end else begin
                num_samples = 8;
              end

              case(cmd)
              CmdOnly, ReadStd, WriteStd: begin
                data_shift = 1;
              end
              ReadDual, WriteDual: begin
                data_shift = 2;
              end
              ReadQuad, WriteQuad: begin
                data_shift = 4;
              end
              default: begin
                data_shift = 1;
              end
              endcase

              for (int i = 0; i < num_samples; i = i + data_shift) begin
                // wait for the sampling edge
                cfg.wait_sck_edge(SamplingEdge);
                // check sio not x or z
                if (cfg.en_monitor_checks) begin
                  `DV_CHECK_CASE_NE(cfg.vif.sio[3:0], 4'bxxxx)
                  `DV_CHECK_CASE_NE(cfg.vif.sio[3:0], 4'bxxxx)
                end

                which_bit_h = cfg.host_bit_dir ? i : 7 - i;
                which_bit_d = cfg.device_bit_dir ? i : 7 - i;
              case(cmd)
              CmdOnly, ReadStd, WriteStd: begin
                // sample sio[0] for tx
                host_byte[which_bit_h] = cfg.vif.sio[0];
                // sample sio[1] for rx
                device_byte[which_bit_d] = cfg.vif.sio[1];
              end // cmdonly,readstd,writestd
              ReadDual, WriteDual: begin
                // sample sio[0] sio[1] for tx bidir
                host_byte[which_bit_h] = cfg.vif.sio[1];
                host_byte[which_bit_h-1] = cfg.vif.sio[0];
                // sample sio[0] sio[1] for rx bidir
                device_byte[which_bit_d] = cfg.vif.sio[1];
                device_byte[which_bit_d-1] = cfg.vif.sio[0];
              end // ReadDual,WriteDual
              ReadQuad, WriteQuad: begin
                // sample sio[0] sio[1] sio[2] sio[3] for tx bidir
                host_byte[which_bit_h] = cfg.vif.sio[3];
                host_byte[which_bit_h-1] = cfg.vif.sio[2];
                host_byte[which_bit_h-2] = cfg.vif.sio[1];
                host_byte[which_bit_h-3] = cfg.vif.sio[0];
                // sample sio[0] sio[1] sio[2] sio[3] for rx bidir
                device_byte[which_bit_d] = cfg.vif.sio[3];
                device_byte[which_bit_d-1] = cfg.vif.sio[2];
                device_byte[which_bit_d-2] = cfg.vif.sio[1];
                device_byte[which_bit_d-3] = cfg.vif.sio[0];
              end // ReadQuad,WriteQuad
              default: begin
                // sample sio[0] for tx
                host_byte[which_bit_h] = cfg.vif.sio[0];
                // sample sio[1] for rx
                device_byte[which_bit_d] = cfg.vif.sio[1];
              end
              endcase

                cfg.vif.host_bit  = which_bit_h;
                cfg.vif.host_byte = host_byte;
               // sending 7 bits will be padded with 0 for the last bit
                if (i == 6 && num_samples == 7) begin
                  which_bit_d = cfg.device_bit_dir ? 7 : 0;
                  device_byte[which_bit_d] = 0;
                end
                cfg.vif.device_bit = which_bit_d;
                cfg.vif.device_byte = device_byte;
              end

              // sending less than 7 bits will not be captured, byte to be re-sent
              if (num_samples >= 7) begin
                host_item.data.push_back(host_byte);
                device_item.data.push_back(device_byte);
              end
              // sending transactions when collect a word data
              if (host_item.data.size == cfg.num_bytes_per_trans_in_mon &&
                  device_item.data.size == cfg.num_bytes_per_trans_in_mon) begin
              if (host_item.first_byte == 1 && cfg.decode_commands == 1)  begin
                cmdtmp = spi_cmd_e'(host_byte);
                `uvm_info(`gfn, $sformatf("spi_monitor: cmdtmp \n%0h", cmdtmp), UVM_DEBUG)
                 end
                 cmd_byte++;
              if (cmd_byte == cfg.num_bytes_per_trans_in_mon)begin
                 cmd = cmdtmp;
                `uvm_info(`gfn, $sformatf("spi_monitor: cmd \n%0h", cmd), UVM_DEBUG)
                 end
                `uvm_info(`gfn, $sformatf("spi_monitor: host packet:\n%0s", host_item.sprint()),
                          UVM_DEBUG)
                `uvm_info(`gfn, $sformatf("spi_monitor: device packet:\n%0s", device_item.sprint()),
                          UVM_DEBUG)
                `downcast(host_clone, host_item.clone());
                `downcast(device_clone, device_item.clone());
                host_analysis_port.write(host_clone);
                device_analysis_port.write(device_clone);
                // write to fifo for re-active env
                req_analysis_port.write(host_clone);
                rsp_analysis_port.write(device_clone);
                // clean items
                host_item   = spi_item::type_id::create("host_item", this);
                device_item = spi_item::type_id::create("device_item", this);
              end
            end // forever
          end: sample_thread
        join_any
        disable fork;
      end
    join
  endtask : collect_curr_trans

  virtual protected task collect_flash_trans();
    fork
      begin: isolation_thread
        spi_item item = spi_item::type_id::create("host_item", this);
        bit [7:0] opcode;
        bit opcode_received;
        fork
          begin: csb_deassert_thread
            wait(cfg.vif.csb[cfg.csb_sel] == 1'b1);
          end
          begin: sample_thread
            opcode_received = 0;
            // for mode 1 and 3, get the leading edges out of the way
            cfg.wait_sck_edge(LeadingEdge);

            // first byte is opcode. opcode or address is always sent on single mode
            sample_flash_one_byte_data(.num_lanes(1), .is_device_rsp(0), .data(opcode));
            opcode_received = 1;
            extract_flash_cmd_info_via_opcode(item, opcode);
            `uvm_info(`gfn, $sformatf("sampled flash opcode: 0x%0h", opcode), UVM_MEDIUM)

            sample_flash_address(cfg.cmd_infos[opcode].addr_bytes, item.address_q);
            req_analysis_port.write(item);

            forever begin
              byte byte_data;
              sample_flash_one_byte_data(.num_lanes(item.num_lanes),
                                         .is_device_rsp(!item.write_command),
                                         .data(byte_data));
              item.payload_q.push_back(byte_data);
            end
          end: sample_thread
        join_any
        disable fork;

        // only send out the item when opcode is fully received, otherwise,
        // it's consider dropped
        if (opcode_received) host_analysis_port.write(item);
      end
    join
  endtask : collect_flash_trans

  virtual function void extract_flash_cmd_info_via_opcode(spi_item item, bit[7:0] opcode);
    `DV_CHECK_FATAL(cfg.cmd_infos.exists(opcode))
    item.item_type = SpiFlashTrans;
    item.opcode = opcode;
    item.num_lanes = cfg.cmd_infos[opcode].num_lanes;
    item.write_command = cfg.cmd_infos[opcode].write_command;
  endfunction : extract_flash_cmd_info_via_opcode

  virtual task sample_flash_one_byte_data(input int num_lanes, input bit is_device_rsp,
                                          output byte data);
    for (int i = 0; i < 8; i += num_lanes) begin
      int which_bit = cfg.host_bit_dir ? i : 7 - i;
      cfg.wait_sck_edge(SamplingEdge);
      data[which_bit] = cfg.vif.sio[0];
      case(num_lanes)
        1: data[which_bit] = is_device_rsp ? cfg.vif.sio[1] : cfg.vif.sio[0];
        2: begin
          data[which_bit]     = cfg.vif.sio[0];
          data[which_bit + 1] = cfg.vif.sio[1];
        end
        4: begin
          data[which_bit]     = cfg.vif.sio[0];
          data[which_bit + 1] = cfg.vif.sio[1];
          data[which_bit + 2] = cfg.vif.sio[2];
          data[which_bit + 3] = cfg.vif.sio[3];
        end
        default: `uvm_fatal(`gfn, $sformatf("Unsupported lanes num 0x%0h", num_lanes))
      endcase
    end
    `uvm_info(`gfn, $sformatf("sampled one byte data for flash: 0x%0h", data), UVM_HIGH)
  endtask : sample_flash_one_byte_data

  // address is 3 or 4 bytes
  virtual task sample_flash_address(input int num_bytes, output bit[7:0] byte_addr_q[$]);
    for (int i = 0; i < num_bytes; i++) begin
      byte addr;
      sample_flash_one_byte_data(.num_lanes(1), .is_device_rsp(0), .data(addr));
      byte_addr_q.push_back(addr);
    end
    `uvm_info(`gfn, $sformatf("sampled flash addr: %p", byte_addr_q), UVM_MEDIUM)
  endtask : sample_flash_address

  virtual task monitor_ready_to_end();
    ok_to_end = cfg.vif.csb[cfg.csb_sel];
    forever begin
      @(cfg.vif.csb[cfg.csb_sel]);
      ok_to_end = cfg.vif.csb[cfg.csb_sel];
    end
  endtask : monitor_ready_to_end

endclass : spi_monitor
