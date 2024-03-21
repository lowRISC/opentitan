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
  bit [CSB_WIDTH-1:0] active_csb;

  // store the data across multiple CSB in case host sends byte transfers
  bit [7:0] generic_mode_host_byte_q[$];
  bit [7:0] generic_mode_device_byte_q[$];

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
    forever collect_trans(phase);
  endtask

  // collect transactions
  virtual protected task collect_trans(uvm_phase phase);
    bit flash_opcode_received;

    wait (cfg.en_monitor);
    wait (&cfg.vif.csb === 0);
    active_csb = cfg.vif.get_active_csb();

    cfg.vif.sck_polarity = cfg.sck_polarity[active_csb];
    cfg.vif.sck_phase = cfg.sck_phase[active_csb];

    host_item   = spi_item::type_id::create("host_item", this);
    device_item = spi_item::type_id::create("device_item", this);
    fork
      begin : isolation_thread
        fork
          begin : csb_deassert_thread
            wait(cfg.vif.csb[active_csb] == 1'b1);
          end
          begin : main_mon_thread
            case (cfg.spi_func_mode)
              SpiModeGeneric: begin
                // indicate that this the first byte in a spi transaction
                host_item.first_byte = 1;
                cmd = CmdOnly;
                cmd_byte = 0;
                collect_curr_trans();
              end
              SpiModeFlash: collect_flash_trans(host_item, flash_opcode_received);
              SpiModeTpm: collect_tpm_trans(host_item);
              default: begin
                `uvm_fatal(`gfn, $sformatf("Invalid mode %s", cfg.spi_func_mode.name))
              end
            endcase
          end : main_mon_thread
        join_any
        disable fork;
      end : isolation_thread
    join
    // write to host_analysis_port
    case (cfg.spi_func_mode)
      SpiModeFlash: begin
        if (flash_opcode_received) begin
          host_analysis_port.write(host_item);
          host_item.mon_item_complete = 1;
        end
      end
      SpiModeTpm: begin
        if (host_item.address_q.size > 0) begin
          host_analysis_port.write(host_item);
          wait(cfg.vif.csb[active_csb] == 1'b1);
        end
      end
      default: ; // do nothing, in SpiModeGeneric, it writes to fifo for each byte
    endcase
  endtask : collect_trans

  virtual protected task collect_curr_trans();
    // for mode 1 and 3, get the leading edges out of the way
    cfg.wait_sck_edge(LeadingEdge, active_csb);
    forever begin : loop_forever
      logic [7:0] host_byte;    // from sio
      logic [7:0] device_byte;  // from sio
      int       which_bit_h;
      int       which_bit_d;
      int       data_shift;
      bit [3:0] num_samples;

      host_item.csb_sel = active_csb;
      device_item.csb_sel = active_csb;

      if (cfg.partial_byte == 1) begin
        num_samples = cfg.bits_to_transfer;
      end else begin
        num_samples = 8;
      end

      case (cmd)
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

      for (int i = 0; i < num_samples; i = i + data_shift) begin : loop_num_samples
        // wait for the sampling edge
        cfg.wait_sck_edge(SamplingEdge, active_csb);
        // check sio not x
        if (cfg.en_monitor_checks) begin
          foreach (cfg.vif.sio[i]) `DV_CHECK_CASE_NE(cfg.vif.sio[i], 1'bx)
        end

        which_bit_h = cfg.host_bit_dir ? i : 7 - i;
        which_bit_d = cfg.device_bit_dir ? i : 7 - i;
        case (cmd)
          CmdOnly, ReadStd, WriteStd: begin
            // sample sio[0] for tx
            host_byte[which_bit_h] = cfg.vif.sio[0];
            // sample sio[1] for rx
            device_byte[which_bit_d] = cfg.vif.sio[1];
          end // cmdonly,readstd,writestd
          ReadDual, WriteDual: begin
            // TODO, update this section if host_bit_dir can be 0
            `DV_CHECK_EQ(cfg.host_bit_dir, 0, "currently assume host_bit_dir is 0")
            `DV_CHECK_EQ(cfg.device_bit_dir, 0, "currently assume device_bit_dir is 0")
            // sample sio[0] sio[1] for tx bidir
            host_byte[which_bit_h -: 2] = cfg.vif.sio[1:0];
            // sample sio[0] sio[1] for rx bidir
            device_byte[which_bit_h -: 2] = cfg.vif.sio[1:0];
          end // ReadDual,WriteDual
          ReadQuad, WriteQuad: begin
            // TODO, update this section if host_bit_dir can be 0
            `DV_CHECK_EQ(cfg.host_bit_dir, 0, "currently assume host_bit_dir is 0")
            `DV_CHECK_EQ(cfg.device_bit_dir, 0, "currently assume device_bit_dir is 0")
            // sample sio[0] sio[1] sio[2] sio[3] for tx bidir
            host_byte[which_bit_h -: 4] = cfg.vif.sio[3:0];
            // sample sio[0] sio[1] sio[2] sio[3] for rx bidir
            device_byte[which_bit_h -: 4] = cfg.vif.sio[3:0];
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
      end : loop_num_samples

      // sending less than 7 bits will not be captured, byte to be re-sent
      if (num_samples >= 7) begin
        generic_mode_host_byte_q.push_back(host_byte);
        generic_mode_device_byte_q.push_back(device_byte);
      end
      // in generic mode, these queue should always have same size
      `DV_CHECK_EQ_FATAL(generic_mode_host_byte_q.size, generic_mode_device_byte_q.size)
      `DV_CHECK_LE(generic_mode_host_byte_q.size, cfg.num_bytes_per_trans_in_mon)
      // sending transactions when collect a word data
      if (generic_mode_host_byte_q.size == cfg.num_bytes_per_trans_in_mon) begin
        host_item.data = generic_mode_host_byte_q;
        device_item.data = generic_mode_device_byte_q;
        generic_mode_host_byte_q.delete();
        generic_mode_device_byte_q.delete();
        if (host_item.first_byte == 1 && cfg.decode_commands == 1)  begin
          cmdtmp = spi_cmd_e'(host_byte);
          `uvm_info(`gfn, $sformatf("spi_monitor: cmdtmp \n%0h", cmdtmp), UVM_DEBUG)
        end
        cmd_byte++;
        if (cmd_byte == cfg.spi_cmd_width)begin
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
    end : loop_forever
  endtask : collect_curr_trans

  virtual protected task collect_flash_trans(spi_item item, ref bit flash_opcode_received);
    int num_addr_bytes;
    flash_opcode_received = 0;
    // for mode 1 and 3, get the leading edges out of the way
    cfg.wait_sck_edge(LeadingEdge, active_csb);

    // first byte is opcode. opcode or address is always sent on single mode
    sample_and_check_byte(.num_lanes(1), .is_device_rsp(0),
                          .data(item.opcode), .check_data_not_z(1));
    flash_opcode_received = 1;
    cfg.extract_cmd_info_from_opcode(item.opcode,
        // output
        num_addr_bytes, item.write_command, item.num_lanes, item.dummy_cycles);
    `uvm_info(`gfn, $sformatf("sampled flash opcode: 0x%0h", item.opcode), UVM_HIGH)

    sample_address(num_addr_bytes, item.address_q);

    repeat (item.dummy_cycles) begin
      cfg.wait_sck_edge(SamplingEdge, active_csb);
    end
    req_analysis_port.write(item);

    forever begin
      logic[7:0] byte_data;
      sample_and_check_byte(item.num_lanes, !item.write_command, byte_data);
      item.payload_q.push_back(byte_data);
    end
  endtask : collect_flash_trans

  virtual protected task collect_tpm_trans(spi_item item);
    uint size;
    bit[7:0] cmd, tpm_rsp;

    cfg.wait_sck_edge(LeadingEdge, active_csb);
    // read the 1st byte to get TPM direction and size
    sample_and_check_byte(.num_lanes(1), .is_device_rsp(0), .data(cmd), .check_data_not_z(1));
    decode_tpm_cmd(cmd, item.write_command, size);
    if (!item.write_command) item.read_size = size;
    `uvm_info(`gfn, $sformatf("Received TPM command: 0x%0x", cmd), UVM_MEDIUM)
    // read 3 bytes address
    fork
      begin : tpm_sio_0
        sample_address(.num_bytes(TPM_ADDR_WIDTH_BYTE), .byte_addr_q(item.address_q));
      end
      begin : tpm_sio_1
        bit[7:0] data;
        // check the data of the last byte is 0, which indicates SPI device in the WAIT state
        for (int i = 0; i < TPM_ADDR_WIDTH_BYTE; i++) begin
          bit last_byte = (i == TPM_ADDR_WIDTH_BYTE - 1);
          sample_and_check_byte(.num_lanes(1), .is_device_rsp(1), .data(data),
                                .check_data_not_z(last_byte));
        end
        `DV_CHECK_EQ(data, 0)
      end
    join
    `uvm_info(`gfn, $sformatf("Received TPM addr: %p", item.address_q), UVM_MEDIUM)
    req_analysis_port.write(item);

    // poll TPM_START
    `DV_SPINWAIT(
      do begin
        cfg.read_byte(.num_lanes(1), .is_device_rsp(1), .csb_id(active_csb), .data(tpm_rsp));
        // current TPM design could only return these values
        `DV_CHECK_FATAL(tpm_rsp inside {TPM_START, TPM_WAIT, '1})
      end while (tpm_rsp[0] == TPM_WAIT);
      , , TPM_START_MAX_WAIT_TIME_NS)
    `uvm_info(`gfn, "Received TPM START", UVM_MEDIUM)

    // sample data
    for (int i = 0; i < size; i++) begin
      sample_and_check_byte(.num_lanes(1), .is_device_rsp(!item.write_command),
                            .data(item.data[i]), .check_data_not_z(1));
      `uvm_info(`gfn, $sformatf("collect %s data for TPM, idx %0d: 0x%0x",
                              item.write_command ? "write" : "read", i, item.data[i]), UVM_MEDIUM)
    end
  endtask

  // address is 3 or 4 bytes
  virtual task sample_address(input int num_bytes, output bit[7:0] byte_addr_q[$]);
    for (int i = 0; i < num_bytes; i++) begin
      byte addr;
      sample_and_check_byte(.num_lanes(1), .is_device_rsp(0),
                            .data(addr), .check_data_not_z(1));
      byte_addr_q.push_back(addr);
    end
    `uvm_info(`gfn, $sformatf("sampled flash addr: %p", byte_addr_q), UVM_HIGH)
  endtask : sample_address

  task sample_and_check_byte(input int num_lanes,
                             input bit is_device_rsp,
                             output logic [7:0] data,
                             input bit check_data_not_z = 0);
    cfg.read_byte(num_lanes, is_device_rsp, active_csb, data);

    if (cfg.en_monitor_checks) begin
      foreach (data[i]) begin
        `DV_CHECK_CASE_NE(data[i], 1'bx)
        if (check_data_not_z) `DV_CHECK_CASE_NE(data[i], 1'bz)
      end
    end
  endtask

  virtual task monitor_ready_to_end();
    ok_to_end = 1;
    forever begin
      @(cfg.vif.csb);
      ok_to_end = (cfg.vif.csb == '1);
    end
  endtask : monitor_ready_to_end

endclass : spi_monitor
