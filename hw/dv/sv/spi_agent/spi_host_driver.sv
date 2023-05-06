// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_driver extends spi_driver;
  `uvm_component_utils(spi_host_driver)
  `uvm_component_new

  uint sck_pulses = 0;
  bit [CSB_WIDTH-1:0] active_csb;

  virtual task run_phase(uvm_phase phase);
    fork
      super.run_phase(phase);
      gen_sck();
    join
  endtask

  // Resets signals
  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n or negedge cfg.vif.disconnected);
      if (cfg.vif.disconnected) continue;
      under_reset = 1'b1;
      active_csb  = 1'b0;
      cfg.vif.sck <= cfg.sck_polarity[0];
      cfg.vif.sio_out <= 'x;
      cfg.vif.csb <= '1;
      sck_pulses = 0;
      @(posedge cfg.vif.rst_n);
      under_reset = 1'b0;
    end
  endtask

  // generate sck
  task gen_sck();
    @(posedge cfg.vif.rst_n);
    forever begin
      if (sck_pulses > 0 || cfg.sck_on) begin
        cfg.vif.sck <= ~cfg.vif.sck;
        #((cfg.sck_period_ps / 2 + get_rand_extra_delay_ns_btw_sck() * 1000) * 1ps);
        cfg.vif.sck <= ~cfg.vif.sck;
        #((cfg.sck_period_ps / 2 + get_rand_extra_delay_ns_btw_sck() * 1000) * 1ps);
        if (sck_pulses > 0) sck_pulses--;
        // dly after a word transfer is completed
        if (sck_pulses % 32 == 0) #(get_rand_extra_delay_ns_btw_word() * 1ns);
      end else begin
        @(cfg.sck_on, sck_pulses);
        if (sck_pulses > 0) begin
          // drive half cycle first
          cfg.vif.sck <= cfg.sck_polarity[active_csb];
          #(cfg.sck_period_ps / 2 * 1ps);
        end
      end
      cfg.vif.sck_pulses = sck_pulses;
    end
  endtask : gen_sck

  task switch_polarity_and_phase();
    if (cfg.vif.sck != cfg.sck_polarity[active_csb]) begin
      cfg.vif.sck <= cfg.sck_polarity[active_csb];
      #TIME_SCK_STABLE_TO_CSB_NS;
    end
  endtask : switch_polarity_and_phase

  task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      `DV_CHECK_EQ(cfg.vif.disconnected, 0)

      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("spi_host_driver: rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      if (cfg.csb_sel_in_cfg) active_csb = cfg.csid;
      else                    active_csb = req.csb_sel;

      switch_polarity_and_phase();
      // switch from x to z to release the IO
      cfg.vif.sio_out <= 'z;

      case (req.item_type)
        SpiTransNormal: begin
          case (cfg.spi_func_mode)
            SpiModeGeneric: drive_normal_item();
            SpiModeFlash: drive_flash_item();
            SpiModeTpm: drive_tpm_item();
            default: begin
              `uvm_fatal(`gfn, $sformatf("Invalid mode %s", cfg.spi_func_mode.name))
            end
          endcase
        end
        SpiTransSckNoCsb: drive_sck_no_csb_item();
        SpiTransCsbNoSck: drive_csb_no_sck_item();
        SpiTransIncompleteOpcode: begin
          // TODO(#15721), need to have at least 3 spi_clk when CSB is active, otherwise,
          // this incomplete req may have bad side effect due to `sys_csb_deasserted_pulse_i`
          // isn't set correctly
          int num_bits = $urandom_range(3, 7);
          // invoke `drive_normal_item` to send less than 8 bits data as incompleted opcode
          drive_normal_item(.partial_byte(1), .num_bits(num_bits));
        end
        default: `uvm_fatal(`gfn, $sformatf("Invalid type %s", req.item_type.name))
      endcase

      cfg.vif.csb[active_csb] <= 1'b1;
      cfg.vif.sio_out <= 'x;

      #($urandom_range(cfg.max_idle_ns_after_csb_drop, cfg.min_idle_ns_after_csb_drop) * 1ns);
      `uvm_info(`gfn, "spi_host_driver: item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

  task issue_data(input bit [7:0] transfer_data[$], output bit [7:0] returned_data[$],
                  input bit last_data = 1, input int num_bits = 8);
    for (int i = 0; i < transfer_data.size(); i++) begin
      bit [7:0] host_byte;
      bit [7:0] device_byte;
      int       which_bit;

      if (transfer_data.size == 0) return;

      host_byte = transfer_data[i];
      for (int j = 0; j < num_bits; j++) begin
        // drive sio early so that it is stable at the sampling edge
        which_bit = cfg.host_bit_dir ? j : 7 - j;
        cfg.vif.sio_out[0] <= host_byte[which_bit];
        // wait for sampling edge to sample sio (half cycle)
        cfg.wait_sck_edge(SamplingEdge, active_csb);
        which_bit = cfg.device_bit_dir ? j : 7 - j;
        device_byte[which_bit] = cfg.vif.sio[1];
        // wait for driving edge to complete 1 cycle
        if (!last_data || i != transfer_data.size() - 1 || j != (num_bits - 1)) begin
          cfg.wait_sck_edge(DrivingEdge, active_csb);
        end
      end
      returned_data[i] = device_byte;
    end
  endtask

  task drive_normal_item(bit partial_byte = cfg.partial_byte,
                         int num_bits = cfg.partial_byte ? cfg.bits_to_transfer : 8);
    cfg.vif.csb[active_csb] <= 1'b0;
    if ((req.data.size() == 1) && (partial_byte == 1)) begin
      sck_pulses = num_bits;
      num_bits = num_bits;
    end else begin
      sck_pulses = req.data.size() * 8;
    end

    // for mode 1 and 3, get the leading edges out of the way
    cfg.wait_sck_edge(LeadingEdge, active_csb);

    // drive data
    issue_data(req.data, rsp.data, , num_bits);

    wait(sck_pulses == 0);
  endtask

  task drive_flash_item();
    bit [7:0] cmd_addr_bytes[$];
    bit [7:0] dummy_return_q[$]; // nothing to return for flash cmd, addr and write

    `uvm_info(`gfn, $sformatf("Driving flash item: \n%s", req.sprint()), UVM_HIGH)
    cfg.vif.csb[active_csb] <= 1'b0;

    cmd_addr_bytes = {req.opcode, req.address_q};
    sck_pulses = cmd_addr_bytes.size() * 8 + req.dummy_cycles;
    if (req.num_lanes > 0) begin
      if (req.write_command) begin
        `DV_CHECK_EQ(req.num_lanes, 1)
        sck_pulses += req.payload_q.size * 8;
      end else begin
        `DV_CHECK_EQ(req.payload_q.size, 0)
        sck_pulses += req.read_size * (8 / req.num_lanes);
      end
    end

    // for mode 1 and 3, get the leading edges out of the way
    cfg.wait_sck_edge(LeadingEdge, active_csb);

    // driver cmd and address
    issue_data(cmd_addr_bytes, dummy_return_q);

    // align to DrivingEdge, if the item has more to send
    if (req.dummy_cycles || req.payload_q.size || req.read_size) begin
      cfg.wait_sck_edge(DrivingEdge, active_csb);
      cfg.vif.sio_out <= 'dz;

      if (req.dummy_cycles > 0) begin
        repeat (req.dummy_cycles) begin
          cfg.wait_sck_edge(SamplingEdge, active_csb);
        end
        if (req.payload_q.size || req.read_size) cfg.wait_sck_edge(DrivingEdge, active_csb);
      end
      // drive data
      if (req.write_command) begin
        issue_data(req.payload_q, dummy_return_q);
      end else begin
        repeat (req.read_size) begin
          logic [7:0] data;
          cfg.read_byte(.num_lanes(req.num_lanes), .is_device_rsp(1),
                        .csb_id(active_csb), .data(data));
          rsp.payload_q.push_back(data);
        end
        `uvm_info(`gfn, $sformatf("collect read data for flash: 0x%p", rsp.payload_q), UVM_HIGH)
      end
    end

    wait(sck_pulses == 0);
  endtask

  task drive_tpm_item();
    bit [7:0] cmd_bytes[$];
    bit [7:0] returned_bytes[$];
    byte data_num_byte;
    bit [7:0] tpm_rsp;

    `uvm_info(`gfn, $sformatf("Driving TPM item: \n%s", req.sprint()), UVM_MEDIUM)

    `DV_CHECK_EQ_FATAL(req.address_q.size(), TPM_ADDR_WIDTH_BYTE)
    // When issuing write command, data size cannot be 0.
    `DV_CHECK(req.data.size() > 0 | !req.write_command)
    data_num_byte = req.write_command ? req.data.size() : req.read_size;
    cmd_bytes = {get_tpm_cmd(req.write_command, data_num_byte), req.address_q};

    cfg.vif.csb[active_csb] <= 1'b0;
    sck_pulses = cmd_bytes.size() * 8;
    issue_data(.transfer_data(cmd_bytes), .returned_data(returned_bytes), .last_data(0));

    // polling TPM_START
    `DV_SPINWAIT(
      do begin
        bit [7:0] dummy_bytes[$];
        dummy_bytes = {$urandom};
        sck_pulses += 8;
        issue_data(.transfer_data(dummy_bytes), .returned_data(returned_bytes), .last_data(0));
        tpm_rsp = returned_bytes[0];
      end while (tpm_rsp[0] == TPM_WAIT);
      , , TPM_START_MAX_WAIT_TIME_NS)

    `uvm_info(`gfn, "Received TPM START", UVM_HIGH)
    sck_pulses += (req.write_command ? req.data.size : req.read_size) * 8;
    if (req.write_command) begin
      issue_data(.transfer_data(req.data), .returned_data(returned_bytes), .last_data(1));
      // no data will return for write
      foreach (returned_bytes[i]) `DV_CHECK_EQ(returned_bytes[i], 0)
    end else begin // TPM read
      bit [7:0] dummy_bytes[$];
      repeat (req.read_size) dummy_bytes.push_back($urandom);
      issue_data(.transfer_data(dummy_bytes), .returned_data(rsp.data), .last_data(1));
      `uvm_info(`gfn, $sformatf("collect read data for TPM: 0x%p", rsp.data), UVM_HIGH)
    end
    wait(sck_pulses == 0);
  endtask

  task drive_sck_no_csb_item();
    repeat (req.dummy_sck_cnt) begin
      #($urandom_range(1, 100) * 1ns);
      cfg.vif.sck <= ~cfg.vif.sck;
    end
  endtask

  task drive_csb_no_sck_item();
    cfg.vif.csb[active_csb] <= 1'b0;
    #(req.dummy_csb_length_ns * 1ns);
  endtask

  function uint get_rand_extra_delay_ns_btw_sck();
    if (cfg.en_extra_dly_btw_sck && ($urandom % 100) < cfg.extra_dly_chance_pc_btw_sck) begin
      return $urandom_range(cfg.min_extra_dly_ns_btw_sck, cfg.max_extra_dly_ns_btw_sck);
    end else begin
      return 0;
    end
  endfunction

  function uint get_rand_extra_delay_ns_btw_word();
    if (cfg.en_extra_dly_btw_word && ($urandom % 100) < cfg.extra_dly_chance_pc_btw_word) begin
      return $urandom_range(cfg.min_extra_dly_ns_btw_word, cfg.max_extra_dly_ns_btw_word);
    end else begin
      return 0;
    end
  endfunction

endclass
