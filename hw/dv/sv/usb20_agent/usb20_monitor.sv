// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_monitor extends dv_base_monitor #(
  .ITEM_T (usb20_item),
  .REQ_ITEM_T (usb20_item),
  .RSP_ITEM_T (usb20_item),
  .CFG_T  (usb20_agent_cfg),
  .COV_T  (usb20_agent_cov)
);
  `uvm_component_utils(usb20_monitor)

   usb20_item     m_usb20_item;
   sof_pkt        m_sof_pkt;
   token_pkt      m_token_pkt;
   data_pkt       m_data_pkt;
   handshake_pkt  m_handshake_pkt;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_usb20_item = usb20_item::type_id::create("m_usb20_item");
    m_sof_pkt = sof_pkt::type_id::create("m_sof_pkt");
    m_token_pkt = token_pkt::type_id::create("m_token_pkt");
    m_data_pkt = data_pkt::type_id::create("m_data_pkt");
    m_handshake_pkt = handshake_pkt::type_id::create("m_handshake_pkt");
    // Complete the event type for the packet objects because these never change.
    m_sof_pkt.m_ev_type = EvPacket;
    m_token_pkt.m_ev_type = EvPacket;
    m_data_pkt.m_ev_type = EvPacket;
    m_handshake_pkt.m_ev_type = EvPacket;
    if (!uvm_config_db#(virtual usb20_block_if)::get(this, "*.env.m_usb20_agent*", "bif",
                                                     cfg.bif)) begin
      `uvm_fatal(`gfn, "failed to get usb20_block_if handle from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*.env", "clk_rst_vif",
                                                 cfg.clk_rst_if_i)) begin
      `uvm_fatal(`gfn, "failed to get clk_rst_if handle from uvm_config_db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    detect_reset();

    // Wait for VBUS assertion; this will be the first attempt of the driver to connect to the DUT;
    // also - importantly - some of the sequences exercise the ability of the DUT to drive the
    // USB lines directly, when the USB is not active. In these tests VBUS has never been asserted,
    // so we shan't attempt to decode - and thus reject - invalid bus states.
    wait_connection();

    forever begin
      usb_symbol_e sym = USB20Sym_J;
      // Number of bit intervals for which the USB has been in Idle state.
      int unsigned idle_time = 0;
      bit disconnected = 0;
      bit suspended = 0;
      bit got_sym = 0;

      // To cope with the frequency delta between the host and the device, both of which are
      // driving the USB, it's important not to sample the bus with a fixed phase, but rather we
      // detect the transition on the bus and then commence symbol capture.
      //
      // We use a parallel process to detect the long duration of Suspend Signaling and thus
      // differentiate the K state of Resume Signaling from the K state of the Start Of Packet.
      //
      // We also detect VBUS/SENSE disconnection using a third process, at which point nothing
      // else may happen on the USB until we observe a reconnection.
      fork begin : isolation_fork
        fork
          // Detect VBUS/SENSE disconnection.
          begin
            wait_disconnection();
            disconnected = 1;
          end
          // Detect the USB being Idle for long enough to constitute Suspend Signaling.
          begin
            while (sym == USB20Sym_J) begin
              // An Idle state for more than 3ms constitutes Suspend Signaling,
              // measured according to the host-side clock; 12Mbps.
              //
              // The DUT does not, however, count its own non-Idle transmission, and it could take
              // ca. 53us to transmit an Isochronous IN packet to the host. It could also be running
              // on a faster clock.
              //
              // We must notify the scoreboard of the Suspend Signaling before the DUT transitions.
              if (idle_time > 2_912 * 12) begin
                // The scoreboard will need to know that the bus has been in Idle state for long
                // enough to suspend.
                if (!suspended) suspend_detected();
                suspended = 1;
              end else idle_time++;
              collect_symbol(sym);
            end
            got_sym = 1;
          end
          // Wait until the USB changes state, away from J state.
          wait_transition();
        join_any
        disable fork;
      end : isolation_fork
      join

      if (disconnected) begin
        disconnection_detected();
        // Wait to be reconnected.
        wait_connection();
      end else begin
        // Do we still need to collect the first non-J sample?
        if (!got_sym) collect_symbol(sym);
        case (sym)
          // K state indicate SOP, or beginning of Resume Signaling.
          USB20Sym_K: begin
            // Packet collection may bail and fall back to interpreting a sustained K state as
            // Resume Signaling.
            bit resuming = 0;
            if (!suspended) begin
              collect_packet(resuming);
            end
            if (suspended || resuming) begin
              collect_resume_signaling();
              suspended = 0;
            end
          end
          // Detection of Bus Resets.
          USB20Sym_SE0: collect_bus_reset();
          USB20Sym_J: `uvm_fatal(`gfn, "J state should be impossible here")
          default: `uvm_fatal(`gfn, "Invalid bus state")
        endcase
      end
    end
  endtask

  // Report the connection event.
  function void connection_detected();
    usb20_item connect = usb20_item::type_id::create("connect");

    `uvm_info(`gfn, "VBUS/SENSE connection", UVM_MEDIUM)
    connect.m_ev_type = EvConnect;
    connect.m_ev_duration_usecs = 0;
    req_analysis_port.write(connect);
  endfunction

  // Wait for VBUS/SENSE connection.
  //
  // Nothing happens on the USB until VBUS/SENSE connection indicating the presence of the USB
  // host, and often the provision of electrical power.
  task wait_connection();
    fork
      begin
        wait (cfg.bif.usb_vbus);
        // Report the assertion of VBUS/SENSE indicating the presence of the USB host controller.
        connection_detected();
        // Wait for device connection; either DP or DN shall be pulled high by the DUT.
        wait_transition();
      end
      // When VBUS is first connected the DP/DN lines are weakly pulled low by the USB host
      // controller and the DUT sees this as a Bus Reset condition.
      collect_bus_reset();
    join
  endtask

  // Notify the scoreboard that a VBUS/SENSE disconnection has occurred.
  function void disconnection_detected();
    usb20_item disconnect = usb20_item::type_id::create("disconnect");

    `uvm_info(`gfn, "VBUS/SENSE disconnection", UVM_MEDIUM)
    disconnect.m_ev_type = EvDisconnect;
    disconnect.m_ev_duration_usecs = 0;
    req_analysis_port.write(disconnect);
  endfunction

  // Wait for VBUS/SENSE disconnection; this task may be disabled by the presence of other
  // USB signaling.
  task wait_disconnection();
    wait (!cfg.bif.usb_vbus);
  endtask

  // Await a transition on the USB.
  task wait_transition();
    // Note: The tx_d_o and tx_se0_o signals are direct-drive DUT outputs; use these only when the
    //       DUT is driving.
    if (cfg.bif.usb_dp_en_o & cfg.tx_use_d_se0) begin
      // D/SE0 signaling is being used by the DUT.
      @(posedge cfg.bif.usb_tx_d_o   or negedge cfg.bif.usb_tx_d_o or
        posedge cfg.bif.usb_tx_se0_o or negedge cfg.bif.usb_tx_se0_o);
    end else begin
      // DP/DN signals are being used directly.
      @(posedge cfg.bif.usb_n or negedge cfg.bif.usb_n or
        posedge cfg.bif.usb_p or negedge cfg.bif.usb_p);
    end
  endtask

  // Report the detection of Suspend Signaling on the USB (Idle state for more than 3ms).
  task suspend_detected();
    usb20_item suspend = usb20_item::type_id::create("suspend");

    `uvm_info(`gfn, "Suspend Signaling detected", UVM_MEDIUM)
    suspend.m_ev_type = EvSuspend;
    suspend.m_ev_duration_usecs = 0;
    req_analysis_port.write(suspend);
  endtask

  // Sample USB DP/DN signals.
  task collect_symbol(output usb_symbol_e sym);
    // Advance to centre of bit interval.
    @(posedge cfg.bif.clk_i);
    @(posedge cfg.bif.clk_i);
    // Return the symbol currently on the bus, according to the pin configuration.
    //
    // Note: The tx_d_o and tx_se0_o signals are direct-drive DUT outputs; use these only when the
    //       DUT is driving.
    if (cfg.bif.usb_dp_en_o & cfg.tx_use_d_se0) begin
      // SE0 takes precedence over the data line.
      sym = cfg.bif.usb_tx_se0_o ? USB20Sym_SE0 : // SE0 unaffected by pin flipping.
          // Pin flipping does affect D/SE0 output too; the sense of 'd' is inverted.
          ((cfg.bif.usb_tx_d_o ^ cfg.pinflip) ? USB20Sym_J : USB20Sym_K);
    end else begin
      casez ({cfg.bif.usb_n, cfg.bif.usb_p})
        2'b00:   sym = USB20Sym_SE0;
        2'b01:   sym = (cfg.pinflip ? USB20Sym_K : USB20Sym_J);
        2'b10:   sym = (cfg.pinflip ? USB20Sym_J : USB20Sym_K);
        default: sym = USB20Sym_Invalid;
      endcase
    end
    // Advance to next bit interval change.
    @(posedge cfg.bif.clk_i);
    @(posedge cfg.bif.clk_i);
  endtask

  // Signal Bus Reset condition to the scoreboard, with the specified duration; a reset condition
  // is at least 2.5 usecs (7.1.7.5).
  function void bus_reset_detected(int unsigned duration_usecs = 4, bit completed = 1'b1);
    usb20_item bus_reset = usb20_item::type_id::create("bus_reset");

    `uvm_info(`gfn, "Bus Reset detected", UVM_MEDIUM)
    bus_reset.m_ev_type = EvBusReset;
    bus_reset.m_ev_duration_usecs = duration_usecs;
    bus_reset.m_ev_completed = completed;
    req_analysis_port.write(bus_reset);
  endfunction

  // Bus Reset detected on the USB.
  virtual task collect_bus_reset();
    int unsigned bit_cnt = 0;
    usb_symbol_e sym;
    collect_symbol(sym);
    // We need to report the Bus Reset after ~3 microseconds (36 bits) and not wait until the end
    // of the Bus Reset to signal its occurrence, otherwise the scoreboard will be informed way
    // too late.
    while (sym == USB20Sym_SE0 && bit_cnt < 36) begin
      bit_cnt++;
      collect_symbol(sym);
    end
    // Bus Reset Signaling requires SE0 state for > 2.5 microseconds.
    if (sym != USB20Sym_SE0) return;

    // TODO: presently we are still relying upon the DUT driver enable to ascertain who is talking;
    // the DUT shall NEVER be generating Bus Reset Signaling.
    `DV_CHECK_EQ(cfg.bif.usb_dp_en_o, 0, "Bus Reset Signaling generated by DUT")
    bus_reset_detected((bit_cnt + 11) / 12, .completed(1'b0));

    // Consume the rest of the Bus Reset, which could be many milliseconds.
    collect_symbol(sym);
    while (sym == USB20Sym_SE0) begin
      bit_cnt++;
      collect_symbol(sym);
    end
    `uvm_info(`gfn, $sformatf("Bus Reset of %d bit intervals detected", bit_cnt), UVM_MEDIUM)
    // Send an update here since this is also required; some of the DUT state changes as soon as a
    // valid Bus Reset is detected, whilst the link state is not updated until the end of Bus Reset
    // Signaling.
    bus_reset_detected((bit_cnt + 11) / 12, .completed(1'b1));
  endtask

  // Signal Resume Signaling to the scoreboard, with the specified duration and indicating whether
  // completion of Resume Signaling has yet occurred.
  function void resume_signaling_detected(int unsigned duration_usecs = 1, bit completed = 1'b0);
    usb20_item resume = usb20_item::type_id::create("resume");

    `uvm_info(`gfn, "Resume Signaling detected", UVM_MEDIUM)
    resume.m_ev_type = EvResume;
    resume.m_ev_duration_usecs = duration_usecs;
    resume.m_ev_completed = completed;
    req_analysis_port.write(resume);
  endfunction

  // Resume Signaling detected on the USB.
  virtual task collect_resume_signaling();
    int unsigned bit_cnt = 0;
    usb_symbol_e sym;
    bit valid;
    collect_symbol(sym);
    // Scoreboard must be notified almost immediately that Resume Signaling has been detected but
    // is not yet completed, so that it can update its prediction of the link state. Resume
    // Signaling typically takes at least 20ms.
    resume_signaling_detected(1, .completed(1'b0));
    while (sym == USB20Sym_K) begin
      bit_cnt++;
      collect_symbol(sym);
    end
    valid = (sym == USB20Sym_SE0);
    // The Resume Signaling ends with a Low Speed EOP (2 SE0 bits and 1 Idle) and is 8 times
    // slower than Full Speed signaling, but we have already collected the first symbol.
    for (int i = 0; i < 15; i++) begin
      collect_symbol(sym);
      valid = valid & (sym == USB20Sym_SE0);
    end
    // TODO: presently we are still relying upon the DUT driver enable to ascertain who is talking;
    // the DUT shall NEVER be generating Resume Signaling.
    `DV_CHECK_EQ(cfg.bif.usb_dp_en_o, 0, "Bus Resume Signaling generated by DUT")
    `uvm_info(`gfn, $sformatf("Resume Signaling of %d bit intervals detected", bit_cnt), UVM_MEDIUM)
    resume_signaling_detected((bit_cnt + 11) / 12, .completed(1'b1));
    // Collect the Low Speed Idle bit too; we must notify the scoreboard after the SE0 but before
    // the lengthy LS Idle bit, otherwise the prediction will be too late.
    for (int i = 15; i < 23; i++) begin
      collect_symbol(sym);
      valid = valid & (sym == USB20Sym_J);
    end
    // Check that the Resume Signaling from the driver is as expected.
    `DV_CHECK_EQ(valid, 1, "Invalid Resume Signaling")
  endtask

//----------------------------------------Collect Packet------------------------------------------//
  virtual task collect_packet(output bit resuming);
    // The first byte of every packet is the SYNC signal to permit DPLLs to lock.
    byte unsigned sync = 8'h2a;
    int unsigned eop_bits = 0;
    bit monitored_decoded_packet[];
    bit destuffed_packet[$];
    int bit_intervals = 0;
    bit valid_stuffing;
    usb_symbol_e sym;
    bit from_driver;
    bit valid_sync;
    bit valid_eop;
    bit packet[$];

    // Assume Resume Signaling until we see a further state change.
    resuming = 1'b1;

    // We have already detected the first K state of the SYNC signaling.
    packet.push_back(1'b0);
    // Who is transmitting?
    from_driver = !cfg.bif.usb_dp_en_o;
    // Keep collecting symbols until we detect something that is neither J nor K,
    // or K state is sufficiently prolonged that we're seeing Resume Signaling.
    collect_symbol(sym);
    while (sym == USB20Sym_J || sym == USB20Sym_K) begin
      // Check whether we have seen only K state for a number of bit intervals.
      if (resuming && sym == USB20Sym_K) begin
        if (++bit_intervals >= 8) begin
          resuming = 1'b1;
          return;
        end
      end else resuming = 1'b0;
      // Collect symbol for packet.
      packet.push_back(sym == USB20Sym_J);
      collect_symbol(sym);
    end
    // TODO: Consider 'dribble' tolerance here.
    // Detect and validate the EOP signaling.
    while (sym == USB20Sym_SE0) begin
      eop_bits++;
      collect_symbol(sym);
    end
    valid_eop = cfg.single_bit_SE0 ? (eop_bits >= 1) : (eop_bits == 2);

    `uvm_info(`gfn, $sformatf("Complete monitored packet = %p", packet), UVM_MEDIUM)

    // We never expect to receive invalid SYNC signals at present; at some point we may generate
    // them from the driver, but the DUT should never generate them.
    `DV_CHECK_GT(packet.size(), 8, "Incomplete SYNC signal detected")
    valid_sync = 1'b1;
    for (int unsigned b = 0; b < 8; b++) begin
      if (packet[b] != sync[b]) begin
        `uvm_info(`gfn, $sformatf("Invalid SYNC signal detected %p", packet), UVM_MEDIUM)
        valid_sync = 1'b0;
      end
    end

    nrzi_decoder(packet, monitored_decoded_packet);
    bit_destuffing(monitored_decoded_packet, valid_stuffing, destuffed_packet);
    classifies_packet(valid_sync, valid_eop, valid_stuffing, destuffed_packet, from_driver);
  endtask

//----------------------------------------Classifies Trans----------------------------------------//
  function void classifies_packet(bit valid_sync, bit valid_eop, bit valid_stuffing,
                                  ref bit destuffed_packet[$], input bit from_driver);
    // Read the Packet IDentifier and check its validity.
    pid_type_e pid_e;
    bit [7:0] pid;
    for (int i = 0; i < 8; i++) begin
      pid[i] = destuffed_packet[i + 8];
    end
    `uvm_info(`gfn, $sformatf(".......Packet PID = %b", pid), UVM_HIGH)
    pid_e = pid_type_e'(pid);
    case (pid)
      // Token PID Types.
      PidTypeOutToken,
      PidTypeInToken,
      PidTypeSetupToken: begin
        `DV_CHECK_EQ(from_driver, 1'b1, "Only driver should transmit token packets")
        token_packet(pid_e, valid_sync, valid_eop, valid_stuffing, destuffed_packet);
      end
      PidTypeSofToken: begin
        `DV_CHECK_EQ(from_driver, 1'b1, "Only driver should transmit SOF packets")
         sof_packet(pid_e, valid_sync, valid_eop, valid_stuffing, destuffed_packet);
      end
      // Data PID Types.
      PidTypeData0,
      PidTypeData1,
      PidTypeData2,
      PidTypeMData: data_packet(pid_e, valid_sync, valid_eop, valid_stuffing,
                                destuffed_packet, from_driver);
      // Handshake PID Types.
      PidTypeAck,
      PidTypeNak,
      PidTypeStall,
      PidTypeNyet: handshake_packet(pid_e, valid_sync, valid_eop, valid_stuffing,
                                    destuffed_packet, from_driver);

      // Invalid PIDs are only those produced by fault injection, or DUT error.
      default: invalid_packet_pid(pid_e, valid_sync, valid_eop, valid_stuffing,
                                  destuffed_packet, from_driver);
    endcase
  endfunction

//-------------------------------------------SOF Packet-------------------------------------------//
  function void sof_packet(pid_type_e pid, bit valid_sync, bit valid_eop, bit valid_stuffing,
                           ref bit destuffed_packet[$]);
    m_sof_pkt.m_pid_type = pid;
    m_sof_pkt.valid_sync = valid_sync;
    m_sof_pkt.valid_eop = valid_eop;
    m_sof_pkt.valid_stuffing = valid_stuffing;
    if (destuffed_packet.size() == 32) begin
      // Unpack everything following the PID.
      {m_sof_pkt.crc5, m_sof_pkt.framenum} = {<<{destuffed_packet[16:31]}};
      if (!m_sof_pkt.valid_crc()) begin
        // Informational report; the scoreboard may check this using `valid_crc().`
        `uvm_info(`gfn, $sformatf("Detected SOF packet CRC5 mismatch (0x%0x, expected 0x%0x)",
                                  m_sof_pkt.crc5, m_sof_pkt.exp_crc()), UVM_MEDIUM)
      end
      m_sof_pkt.valid_length = 1;
    end else m_sof_pkt.valid_length = 0;

    req_analysis_port.write(m_sof_pkt);
  endfunction

//------------------------------------------Token Packet------------------------------------------//
  function void token_packet(pid_type_e pid, bit valid_sync, bit valid_eop, bit valid_stuffing,
                             ref bit destuffed_packet[$]);
    m_token_pkt.m_pid_type = pid;
    m_token_pkt.valid_sync = valid_sync;
    m_token_pkt.valid_eop = valid_eop;
    m_token_pkt.valid_stuffing = valid_stuffing;
    if (destuffed_packet.size() == 32) begin
      // Unpack everything following the PID.
      {m_token_pkt.crc5, m_token_pkt.endpoint, m_token_pkt.address} = {<<{destuffed_packet[16:31]}};
      if (!m_token_pkt.valid_crc()) begin
        // Informational report; the scoreboard may check this using `valid_crc().`
        `uvm_info(`gfn, $sformatf("Detected token packet CRC5 mismatch (0x%0x, expected 0x%0x)",
                                  m_token_pkt.crc5, m_token_pkt.exp_crc()), UVM_MEDIUM)
      end
      m_token_pkt.valid_length = 1;
    end else m_token_pkt.valid_length = 0;

    req_analysis_port.write(m_token_pkt);
  endfunction

//------------------------------------------Data Packet-------------------------------------------//
  function void data_packet(pid_type_e pid, bit valid_sync, bit valid_eop, bit valid_stuffing,
                            ref bit destuffed_packet[$], input bit from_driver);
    // Converting complete packet into transaction level (field wise)
    // Data_PID
    m_data_pkt.m_pid_type = pid;
    m_data_pkt.valid_sync = valid_sync;
    m_data_pkt.valid_eop = valid_eop;
    m_data_pkt.valid_stuffing = valid_stuffing;
    if (destuffed_packet.size() >= 32 && !(destuffed_packet.size() & 7)) begin
      // Collect the data bytes, converting from LSB first to an array of bytes.
      int unsigned len_bits = destuffed_packet.size() - 32;
      byte unsigned data[];
      if (len_bits) begin // Avoid issues with empty part-select.
        data = new [len_bits >> 3];
        data = {<<{destuffed_packet[16:15+len_bits]}}; // Bit-reverse the entire data field.
      end
      m_data_pkt.data = {<<8{data}}; // Reverse the order of the bytes.
      // Collect the actual CRC16.
      m_data_pkt.crc16 = {<<{destuffed_packet[16+len_bits:31+len_bits]}};
      if (!m_data_pkt.valid_crc()) begin
        // Informational report; the scoreboard may check this using `valid_crc().`
        `uvm_info(`gfn, $sformatf("Detected DATA packet CRC16 mismatch (0x%0x, expected 0x%0x)",
                                  m_data_pkt.crc16, m_data_pkt.exp_crc()), UVM_MEDIUM)
      end
      m_data_pkt.valid_length = 1;
    end else m_data_pkt.valid_length = 0;

    if (from_driver) req_analysis_port.write(m_data_pkt);
    else rsp_analysis_port.write(m_data_pkt);
  endfunction

//----------------------------------------Handshake Packet----------------------------------------//
  function void handshake_packet(pid_type_e pid, bit valid_sync, bit valid_eop, bit valid_stuffing,
                                 ref bit destuffed_packet[$], input bit from_driver);
    m_handshake_pkt.m_pid_type = pid;
    m_handshake_pkt.valid_sync = valid_sync;
    m_handshake_pkt.valid_eop = valid_eop;
    m_handshake_pkt.valid_stuffing = valid_stuffing;
    if (destuffed_packet.size() == 16) begin
      m_handshake_pkt.valid_length = 1;
    end else m_handshake_pkt.valid_length = 0;

    if (from_driver) req_analysis_port.write(m_handshake_pkt);
    else rsp_analysis_port.write(m_handshake_pkt);
  endfunction

  //----------------------------------------Invalid Packet----------------------------------------//
  function void invalid_packet_pid(pid_type_e pid, bit valid_sync, bit valid_eop,
                                   bit valid_stuffing, ref bit destuffed_packet[$],
                                   input bit from_driver);
    int unsigned size = destuffed_packet.size();
    `uvm_info(`gfn, $sformatf("packet size = %d", size), UVM_HIGH)
    case (size)
      16: handshake_packet(pid, valid_sync, valid_eop, valid_stuffing, destuffed_packet,
                           from_driver);
      32: begin
        `DV_CHECK_EQ(from_driver, 1'b1, "Only driver should transmit token packets")
        token_packet(pid, valid_sync, valid_eop, valid_stuffing, destuffed_packet);
      end
      default: data_packet(pid, valid_sync, valid_eop, valid_stuffing, destuffed_packet,
                           from_driver);
    endcase
  endfunction

  // NRZI decoder
  task nrzi_decoder(input bit nrzi_in[], output bit monitored_decoded_packet[]);
    bit prev_bit = 1'b1;
    monitored_decoded_packet = new[nrzi_in.size()];
    for (int i = 0; i < nrzi_in.size(); i++) begin
      if (nrzi_in[i] == prev_bit) begin
        // If the current NRZI bit matches the previous bit, it's a 0.
        monitored_decoded_packet[i] = 1'b1;
      end else begin
        // If the current NRZI bit is different from the previous bit, it's a 1.
        monitored_decoded_packet[i] = 1'b0;
      end
      prev_bit = nrzi_in[i];
    end
    `uvm_info(`gfn, $sformatf("Monitored NRZI Decoded Packet = %p", monitored_decoded_packet),
              UVM_HIGH)
  endtask

  // Bit Destuffing
  task bit_destuffing(input bit packet[], output bit valid_stuffing,
                      output bit packet_destuffed[$]);
    int unsigned consecutive_ones_count = 0;
    int i;

    // Clear the validity flag if we encounter any violations whilst destuffing.
    valid_stuffing = 1;

    for (i = 0; i < packet.size(); i++) begin
      if (consecutive_ones_count >= 6) begin
        if (packet[i] != 1'b0) begin
          `uvm_info(`gfn, $sformatf("Bit stuffing violation detected in %p at bit %d",
                                    packet, i), UVM_LOW)
          valid_stuffing = 0;
        end
        consecutive_ones_count = 0;
      end else begin
        packet_destuffed.push_back(packet[i]); // Add the current bit to the destuffed packet.
        if (packet[i] == 1'b1) consecutive_ones_count = consecutive_ones_count + 1;
        else consecutive_ones_count = 0;
      end
    end
    if (consecutive_ones_count >= 6) begin
      `uvm_info(`gfn, $sformatf("Bit stuffing violation detected in %p at bit %d", packet, i),
                UVM_LOW)
      valid_stuffing = 0;
    end
    `uvm_info(`gfn, $sformatf("Monitored Destuffed Packet = %p", packet_destuffed), UVM_HIGH)
  endtask

  // Reset detection
  task detect_reset();
    bit next_rst_phase = 1'b1;
    @(posedge cfg.bif.clk_i);

    while (cfg.bif.rst_ni != next_rst_phase) @(posedge cfg.bif.clk_i);

    // Initially we have have only posedge so assigning 0 to negedge bit because it never detects
    // the negedge of the clk.
    cfg.clk_rst_if_i.wait_for_reset(0, 1);
  endtask
endclass
