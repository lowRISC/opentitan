// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_scoreboard extends cip_base_scoreboard #(
  .CFG_T(usbdev_env_cfg),
  .RAL_T(usbdev_reg_block),
  .COV_T(usbdev_env_cov)
);
  `uvm_component_utils(usbdev_scoreboard)

  // Prediction and checking of the loosely-timed registers.
  usbdev_timed_regs timed_regs;

  // BFM state information for the loosely-timed registers.
  typedef struct {
    uvm_reg_data_t r[usbdev_timed_regs::timed_reg_e];
  } bfm_timed_regs_t;

  // Previous state
  bfm_timed_regs_t prev_timed_regs;

  // Model of USBDEV.
  usbdev_bfm bfm;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(usb20_item) req_usb20_fifo;
  uvm_tlm_analysis_fifo #(usb20_item) rsp_usb20_fifo;

  // Local queue of expected responses from the DUT.
  local usb20_item expected_rsp_q[$];

  // Mask reflecting all of the defined DUT interrupts.
  localparam int unsigned IntrMask = {NumUsbdevInterrupts{1'b1}};

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    // Note: presently the functional model in the scoreboard does not have a concept of elapsed
    // time and the capacity to change state when nothing has happened, eg. if a handshake from the
    // USB host controller is not received within the timeout interval.
    //
    // It is therefore necessary to disable the read data checking of 'configin_' registers for
    // the couple of sequences affected:
    // - `usbdev_device_timeout`
    // - `usbdev_timeout_missing_host_handshake`
    cfg.en_scb_rdchk_configin = 1'b1;
    void'($value$plusargs("en_scb_rdchk_configin=%0b", cfg.en_scb_rdchk_configin));

    // Similarly for the checking of the `intr_state.link_in_err` field, which is asserted by the
    // DUT if there is no handshake to an IN transaction.
    // - `usbdev_device_timeout`
    // - `usbdev_timeout_missing_host_handshake`
    cfg.en_scb_rdchk_link_in_err = 1'b1;
    void'($value$plusargs("en_scb_rdchk_link_in_err=%0b", cfg.en_scb_rdchk_link_in_err));

    // Model cannot be used to predict `intr_state.link_resume` field for a couple of AON/Wake
    // sequences because they deliberately abuse the bus by changing the pin configuration and
    // attempting to change pull up enables whilst the AON/Wake module is active.
    cfg.en_scb_rdchk_link_resume = 1'b1;
    void'($value$plusargs("en_scb_rdchk_link_resume=%0b", cfg.en_scb_rdchk_link_resume));

    // Model cannot be used to predict transitional `link_state` reliably because of CDC and
    // filtering propagation delays in the presence of an asynchronous process that is reading
    // the `usbstat` register repeatedly:
    // - `usbdev_rand_bus_disconnects`
    cfg.en_scb_rdchk_linkstate = 1'b1;
    void'($value$plusargs("en_scb_rdchk_linkstate=%0b", cfg.en_scb_rdchk_linkstate));

    // Monitor and model cannot be used to predict with absolute certainty when a PID/CRC error
    // will be reported when truncating a packet transmission to the DUT because `usb_fs_rx` can
    // sample the SE0 state of a spontaneous Bus Reset and complete the PID even though not all
    // of the PID bits were transmitted. The CRC can simply be a false positive match,
    // particularly the CRC5 of a token packet.
    // Reporting of bit stuffing violations is a similar situation to that with PID bits; whether or
    // not they will be detected and reported is data-dependent.
    cfg.en_scb_rdchk_rx_pid_err = 1'b1;
    void'($value$plusargs("en_scb_rdchk_rx_pid_err=%0b", cfg.en_scb_rdchk_rx_pid_err));
    cfg.en_scb_rdchk_rx_crc_err = 1'b1;
    void'($value$plusargs("en_scb_rdchk_rx_crc_err=%0b", cfg.en_scb_rdchk_rx_crc_err));
    cfg.en_scb_rdchk_rx_bitstuff_err = 1'b1;
    void'($value$plusargs("en_scb_rdchk_rx_bitstuff_err=%0b", cfg.en_scb_rdchk_rx_bitstuff_err));

    super.build_phase(phase);
    // Bus Functional Model of USBDEV.
    bfm = new();
    // Prediction and checking of loosely-timed registers.
    timed_regs = new("timed_regs");
    timed_regs.clk_rst_vif = cfg.clk_rst_vif;
    timed_regs.ral = ral;
    // Checking of USB traffic of the DUT against that of the model.
    req_usb20_fifo = new("req_usb20_fifo", this);
    rsp_usb20_fifo = new("rsp_usb20_fifo", this);
    // Ensure that the BFM has been initialized post-reset.
    bfm.dut_reset();
    init_timed_regs();
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    if (cfg.en_scb) begin
      fork
        process_usb20_req();
        process_usb20_rsp();
        // Prediction checker will discard any predictions over a DUT reset since they can no longer
        // be considered relevant; the CSR state will be reset.
        timed_regs.check_predictions(cfg.under_reset);
        handle_resets();
      join_none
    end
  endtask

  // Handle DUT resets and ensure that the BFM is informed.
  virtual task handle_resets();
    forever begin
      wait (cfg.under_reset);
      bfm.dut_reset();
      // Capture the post-reset state of the loosely-timed registers.
      capture_timed_regs(prev_timed_regs);
      wait (!cfg.under_reset);
    end
  endtask

  // Receive and model the request from the host/driver to the DUT.
  virtual task process_usb20_req();
    usb20_item item;
    forever begin
      // Does the model presently have any timed activity pending?
      if (bfm.timing()) begin
        if (!req_usb20_fifo.try_get(item)) begin
          // Delayed response to received packet, if any.
          usb20_item rsp;
          cfg.clk_rst_vif.wait_clks(1);
          // Inform the model of the passage of time (in terms of DUT clock ticks) and post an
          // expectation of a delayed response, if appropriate.
          if (bfm.send_delayed_response(rsp)) begin
            expected_rsp_q.push_back(rsp);
            update_timed_regs();
          end
          continue;
        end
      end else begin
        // Since we presently do not ever transition from '!timing -> timing' in response to CSR
        // activity, we can safely block until the monitor informs us that something else has
        // happened on the USB; with a more sophisticated model of Idle bus time this may not be
        // possible.
        req_usb20_fifo.get(item);
      end
      if (item.m_ev_type == EvPacket) begin
        // Ignore all USB packets if the DUT is under reset.
        if (cfg.under_reset) begin
          `uvm_info(`gfn, $sformatf("Ignoring monitor packet (PID 0x%0x) because of IP reset",
                                    item.m_pid_type), UVM_LOW)
          continue;
        end
      end else if (expected_rsp_q.size() > 0) begin
        // Any non-packet event signaled by the monitor invalidates any response packets that the
        // functional model has already predicted; this occurs only if a transaction is interrupted.
        `uvm_info(`gfn, $sformatf("Dropping expected response(s) because of bus event %p",
                                  item.m_ev_type), UVM_LOW)
        expected_rsp_q.delete();
      end
      case (item.m_ev_type)
        // Non-packet events on the USB.
        EvBusReset: begin
          `uvm_info(`gfn, $sformatf("Bus Reset received from monitor (completed %0d)",
                                    item.m_ev_completed), UVM_MEDIUM)
          bfm.bus_reset(item.m_ev_completed);
          update_timed_regs();
        end
        EvSuspend: begin
          `uvm_info(`gfn, "Suspend Signaling received from monitor", UVM_MEDIUM)
          bfm.bus_suspend();
          update_timed_regs();
        end
        EvResume: begin
          `uvm_info(`gfn, $sformatf("Resume Signaling received from monitor (completed %0d)",
                                    item.m_ev_completed), UVM_MEDIUM)
          bfm.bus_resume(item.m_ev_completed);
          update_timed_regs();
        end
        EvDisconnect: begin
          `uvm_info(`gfn, "VBUS Disconnection received from monitor", UVM_MEDIUM)
          bfm.bus_disconnect();
          update_timed_regs();
        end
        EvConnect: begin
          `uvm_info(`gfn, "VBUS Connection received from monitor", UVM_MEDIUM)
          bfm.bus_connect();
          update_timed_regs();
        end
        // Packet handling.
        EvPacket: begin
          // Response to received packet, if any.
          usb20_item rsp;
          // Driver -> DUT traffic is just passed to the BFM to update its internal state.
          case (item.m_pkt_type)
            PktTypeSoF: begin
              sof_pkt sof;
              `uvm_info(`gfn, $sformatf("SOF packet (PID 0x%0x) received from monitor",
                                        item.m_pid_type), UVM_MEDIUM)
              `downcast(sof, item);
              collect_sof_cov(sof);
              bfm.sof_packet(sof);
              update_timed_regs();
            end
            PktTypeToken: begin
              token_pkt token;
              `uvm_info(`gfn, $sformatf("Token packet (PID 0x%0x) received from monitor",
                                        item.m_pid_type), UVM_MEDIUM)
              `downcast(token, item);
              collect_token_cov(token);
              if (bfm.token_packet(token, rsp)) expected_rsp_q.push_back(rsp);
              update_timed_regs();
            end
            PktTypeData: begin
              data_pkt data;
              `uvm_info(`gfn, $sformatf("Data packet (PID 0x%0x) received from monitor",
                                        item.m_pid_type), UVM_MEDIUM)
              `downcast(data, item);
              collect_out_data_cov(data);
              if (bfm.data_packet(data, rsp)) expected_rsp_q.push_back(rsp);
              update_timed_regs();
            end
            PktTypeHandshake: begin
              handshake_pkt handshake;
              `uvm_info(`gfn, $sformatf("Handshake packet (PID 0x%0x) received from monitor",
                                        item.m_pid_type), UVM_MEDIUM)
              `downcast(handshake, item);
              collect_handshake_cov(handshake);
              bfm.handshake_packet(handshake);
              update_timed_regs();
            end
            // The BFM does not need to know about Special PIDs since the DUT shall ignore them.
            default: `uvm_info(`gfn, "Special PID packet received from monitor", UVM_DEBUG)
          endcase
        end
        default: `uvm_fatal(`gfn, $sformatf("Invalid/unexpected event type %p", item.m_ev_type))
      endcase
    end
  endtask

  // -------------------------------
  virtual task process_usb20_rsp();
    usb20_item act_item;
    usb20_item exp_item;
    forever begin
      // Collect an actual response from the DUT.
      rsp_usb20_fifo.get(act_item);
      // Ignore all DUT response packets if the DUT is under reset or disconnected from the USB;
      // they will be incomplete responses when the reset/disconnection interrupted a transaction.
      if (cfg.under_reset || !cfg.m_usb20_agent_cfg.bif.usb_vbus) continue;
      // Collect coverage for IN traffic from the DUT.
      collect_dut_rsp_cov(act_item);
      `uvm_info(`gfn, "Comparing DUT response against the BFM expected response:", UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf(" - Actual:\n%0s", act_item.sprint()), UVM_MEDIUM)
      `DV_CHECK_GT(expected_rsp_q.size(), 0, "Unexpected response from DUT; no expectation ready")
      // Compare it against the expected response.
      exp_item = expected_rsp_q.pop_front();
      `uvm_info(`gfn, $sformatf(" - Expected:\n%0s", exp_item.sprint()), UVM_MEDIUM)
      `DV_CHECK_EQ(act_item.compare(exp_item), 1, "DUT response does not match expectation")
    end
  endtask

  // Collection of functional coverage for SOF packets received by the DUT.
  function void collect_sof_cov(ref sof_pkt sof);
    if (!cfg.en_cov) return;
    cov.pids_to_dut_cg.sample(sof.m_pid_type);
    cov.framenum_rx_cg.sample(sof.framenum);
  endfunction

  // Collection of functional coverage for Token packets received by the DUT.
  function void collect_token_cov(ref token_pkt token);
    pid_type_e pid = token.m_pid_type;
    bit [3:0] ep = token.endpoint;
    bit dir_in = (pid == PidTypeInToken);
    if (!cfg.en_cov) return;
    // When the usb20_monitor decodes and forwards Low Speed traffic the PID does not reflect the
    // PRE token used on the USB.
    if (token.low_speed) pid = PidTypePre;  // Coverage should show that PRE has been received.
    cov.pids_to_dut_cg.sample(pid);
    cov.address_cg.sample(token.address, ep);
    cov.crc5_cg.sample(dir_in, token.crc5);
    if (ep < NEndpoints) begin
      if (dir_in) begin
        // Sample IN requests from the DUT -> host.
        cov.ep_in_cfg_cg.sample(pid, bfm.ep_in_enable[ep], bfm.in_stall[ep],
                                bfm.in_iso[ep]);
      end else begin
        // Sample OUT traffic from the host -> DUT.
        cov.ep_out_cfg_cg.sample(pid, bfm.ep_out_enable[ep], bfm.rxenable_setup[ep],
                                 bfm.rxenable_out[ep], bfm.set_nak_out[ep], bfm.out_stall[ep],
                                 bfm.out_iso[ep]);
      end
    end
    cov.pid_type_endp_cg.sample(pid, token.endpoint);
    // SETUP/OUT DATA packets interact with the AvSetup/AvOUT and RX FIFOs.
    if (pid == PidTypeSetupToken || pid == PidTypeOutToken) begin
      cov.fifo_lvl_cg.sample(pid, bfm.avsetup_fifo.size(), bfm.avout_fifo.size(),
                             bfm.rx_fifo.size());
    end
  endfunction

  // Collection of functional coverage for DATA packets received by the DUT.
  function void collect_out_data_cov(ref data_pkt data);
    pid_type_e pid = data.m_pid_type;
    if (!cfg.en_cov) return;
    // When the usb20_monitor decodes and forwards Low Speed traffic the PID does not reflect the
    // PRE token used on the USB.
    if (data.low_speed) pid = PidTypePre;  // Coverage should show that PRE has been received.
    cov.pids_to_dut_cg.sample(pid);
    cov.crc16_cg.sample(.dir_in(1'b0), .crc16(data.crc16));
    cov.data_pkt_cg.sample(.dir_in(1'b0), .pkt_len(data.data.size()));
    // The endpoint number for the OUT DATA transfer is sent in the preceding OUT token packet,
    // if there was one and it was valid.
    if (bfm.rx_token != null) begin
      cov.data_tog_endp_cg.sample(pid, .dir_in(1'b0), .endp(bfm.rx_token.endpoint));
    end
  endfunction

  // Collection of functional coverage for Handshake packets received by the DUT.
  function void collect_handshake_cov(ref handshake_pkt handshake);
    pid_type_e pid = handshake.m_pid_type;
    if (!cfg.en_cov) return;
    // When the usb20_monitor decodes and forwards Low Speed traffic the PID does not reflect the
    // PRE token used on the USB.
    if (handshake.low_speed) pid = PidTypePre;  // Coverage should show that PRE has been received.
    cov.pids_to_dut_cg.sample(pid);
    // The endpoint to which the handshake is sent has been retained from the IN token packet.
    if (bfm.tx_ep != usbdev_bfm::InvalidEP) begin
      cov.data_tog_endp_cg.sample(handshake.m_pid_type, .dir_in(1'b1), .endp(bfm.tx_ep));
    end
  endfunction

  // Collection of functional coverage for DUT responses.
  function void collect_dut_rsp_cov(ref usb20_item item);
    if (!cfg.en_cov) return;
    cov.pids_from_dut_cg.sample(item.m_pid_type);
    case (item.m_pid_type)
      // IN DATA packets transmitted by the DUT.
      PidTypeData0, PidTypeData1: begin
        data_pkt data;
        `downcast(data, item);
        cov.crc16_cg.sample(.dir_in(1'b1), .crc16(data.crc16));
        cov.data_pkt_cg.sample(.dir_in(1'b1), .pkt_len(data.data.size()));
        // The endpoint number for the IN DATA transfer is sent in the preceding token packet,
        // if there was one and it was valid.
        if (bfm.tx_ep != usbdev_bfm::InvalidEP) begin
          cov.data_tog_endp_cg.sample(item.m_pid_type, .dir_in(1'b1), .endp(bfm.tx_ep));
        end
      end
      // Handshake packets sent by the DUT.
      PidTypeAck, PidTypeNak: begin
        // The endpoint number for the IN DATA transfer is sent in the preceding token packet,
        // if there was one and it was valid.
        if (bfm.tx_ep != usbdev_bfm::InvalidEP) begin
          cov.data_tog_endp_cg.sample(item.m_pid_type, .dir_in(1'b1), .endp(bfm.tx_ep));
        end
        // The endpoint number for the OUT DATA transfer is sent in the preceding token packet;
        // if there was one and it was valid the BFM will have retained the endpoint number since
        // it is not present in the DUT response.
        if (bfm.rx_ep != usbdev_bfm::InvalidEP) begin
          cov.data_tog_endp_cg.sample(item.m_pid_type, .dir_in(1'b0), .endp(bfm.rx_ep));
        end
      end
      default: begin
        // Nothing more to do for other packet types.
      end
    endcase
  endfunction

  function void init_timed_regs();
    bfm_timed_regs_t init_regs;
    usbdev_timed_regs::timed_reg_e r;
    // Capture the initial state of the loosely-timed registers.
    capture_timed_regs(init_regs);
    // Remember the register state.
    prev_timed_regs = init_regs;
    // Create the register descriptions.
    r = r.first();
    forever begin
      timed_reg tr = timed_reg::type_id::create("tr");
      uvm_reg_data_t init_val = 0;
      dv_base_reg_field fields[$];
      // Collect the field descriptions for this register.
      case (r)
        usbdev_timed_regs::TimedIntrState:  ral.intr_state.get_dv_base_reg_fields(fields);
        usbdev_timed_regs::TimedUsbStat:    ral.usbstat.get_dv_base_reg_fields(fields);
        usbdev_timed_regs::TimedInSent:     ral.in_sent[0].get_dv_base_reg_fields(fields);
        usbdev_timed_regs::TimedWakeEvents: ral.wake_events.get_dv_base_reg_fields(fields);

        usbdev_timed_regs::TimedConfigIn0,  usbdev_timed_regs::TimedConfigIn1,
        usbdev_timed_regs::TimedConfigIn2,  usbdev_timed_regs::TimedConfigIn3,
        usbdev_timed_regs::TimedConfigIn4,  usbdev_timed_regs::TimedConfigIn5,
        usbdev_timed_regs::TimedConfigIn6,  usbdev_timed_regs::TimedConfigIn7,
        usbdev_timed_regs::TimedConfigIn8,  usbdev_timed_regs::TimedConfigIn9,
        usbdev_timed_regs::TimedConfigIn10, usbdev_timed_regs::TimedConfigIn11: begin
          int unsigned index = r - usbdev_timed_regs::TimedConfigIn0;
          ral.configin[index].get_dv_base_reg_fields(fields);
        end
        default: `uvm_fatal(`gfn, "Invalid/unknown register")
      endcase
      // Report the initial value of this register as predicted by the BFM.
      `uvm_info(`gfn, $sformatf("Reg %p : initial value 0x%0x", r, init_regs.r[r]), UVM_MEDIUM)
      // Collect the initial values of the register fields, dropping any that we cannot predict.
      for (int unsigned f = 0; f < fields.size(); f++) begin
        string field_name = fields[f].get_name();
        // Maximum delay (in DUT clock cycles) for a prediction to be met; most delays should take
        // only a few cycles for internal changes to propagate, but some are substantially longer
        // oweing to the immediate operation of the functional model.
        int unsigned max_delay = 16;
        bit include_field = 1'b1;
        // There are a few fields that we cannot predict because the BFM does not have an
        // appropriate concept of time and does not mimic the invention of bus frames.
        //
        // Note: The DUT will continue to produce frame interrupts and supply frame numbers via
        //       `usbstat` even though SOF frames are not being received from the USB host
        //       controller.
        case (r)
          usbdev_timed_regs::TimedIntrState: begin
            include_field = !(field_name inside {"host_lost", "frame"});
            case (field_name)
              // Isochronous IN packets do not receive an ACKnowledgement so the BFM asserts the
              // `pkt_sent` interrupt state much sooner than the DUT, which waits until the
              // data has been transmitted. 64 bytes to transmit => 4*(4+32+64*8*7/6) clock cycles.
              "pkt_sent": max_delay = 2800;
              // Link reset may arrive 2 microseconds behind the signaling from the monitor, but we
              // must also allow for the different clock frequencies; 2us is 96 clock cycles, extend
              // to 100.
              "link_reset": max_delay = 100;
              // The monitor is compelled to signal the transition to Suspended as much as 90
              // microseconds before the DUT transitions, because the DUT ignores its own non-Idle
              // signaling in timing the Suspend signaling and the DUT could be running faster.
              //
              // 90 usecs x 48 clks/usec => 4320 clocks, and adjust for the possibility that
              // actually the host is running faster.
              "link_suspend": max_delay = 4364;
              // Link resume signaling may be delayed until after the Low Speed EOP.
              "link_resume": begin
                // Checking of the `link_resume` assertion is presently not possible with the
                // functional model for the sequences `usbdev_aon_wake` and
                // `usbdev_aon_wake_disconnect` because they attempt to perturb the pullup enables
                // by changing the bus configuration whilst the AON/Wake module is controlling the
                // bus.
                if (cfg.en_scb_rdchk_link_resume) max_delay = 3 * 8 * 4;
                else include_field = 1'b0;
              end
              "rx_crc_err": begin
                // Monitor and model cannot be used to predict with absolute certainty when a
                // PID/CRC error will be reported when truncating a packet transmission to the DUT
                // because `usb_fs_rx` can sample the SE0 state of a spontaneous Bus Reset and
                // complete the PID even though not all of the PID bits were transmitted. The CRC
                // can simply be a false positive match, particularly the CRC5 of a token packet.
                // Reporting of bit stuffing violations is a similar situation to that with PID
                // bits; whether or not they will be detected and reported is data-dependent.
                if (!cfg.en_scb_rdchk_rx_crc_err) include_field = 1'b0;
              end
              "rx_pid_err": begin
                // See `rx_crc_err` above.
                if (!cfg.en_scb_rdchk_rx_pid_err) include_field = 1'b0;
              end
              "rx_bitstuff_err": begin
                // See `rx_crc_err` above.
                if (!cfg.en_scb_rdchk_rx_bitstuff_err) include_field = 1'b0;
              end
              // Most interrupts should be reflected almost immediately.
              default: begin
                max_delay = 16;
                // Checking of the `link_in_err` assertion following a missing host handshake is
                // not possible presently because the model has no awareness of elapsed time without
                // activity.
                if (!cfg.en_scb_rdchk_link_in_err && field_name == "link_in_err") begin
                  include_field = 1'b0;
                end
              end
            endcase
          end

          usbdev_timed_regs::TimedUsbStat: begin
            include_field = !(field_name inside {"frame", "host_lost"});
            if (field_name == "link_state") begin
              if (cfg.en_scb_rdchk_linkstate)
                // See TimedIntrState.link_suspend explanation above.
                max_delay = 4364;
              else begin
                // `usbdev_rand_bus_disconnects` induces a transitional link state that may or may
                // not be observed, so the model cannot reliably predice the `link_state` field yet.
                include_field = 1'b0;
              end
            end
          end

          // See IntrState.pkt_sent explanation above re Isochronous IN transactions.
          usbdev_timed_regs::TimedInSent: max_delay = 2800;

          // Transitions on the `wake_events` signal may take as long as seven ticks of the AON
          // clock which could be as slow as 160kHz in the DV environment, so ca. 300 cycles per
          // AON cycle but the USBDEV clock is also somewhat variable.
          // - `module_active` can take 3 cycles to change.
          // - `bus_not_idle` has a 4 cycle filter in `usbdev_aon_wake` and 2-flop CDC.
          usbdev_timed_regs::TimedWakeEvents: max_delay = 2300;

          usbdev_timed_regs::TimedConfigIn0,  usbdev_timed_regs::TimedConfigIn1,
          usbdev_timed_regs::TimedConfigIn2,  usbdev_timed_regs::TimedConfigIn3,
          usbdev_timed_regs::TimedConfigIn4,  usbdev_timed_regs::TimedConfigIn5,
          usbdev_timed_regs::TimedConfigIn6,  usbdev_timed_regs::TimedConfigIn7,
          usbdev_timed_regs::TimedConfigIn8,  usbdev_timed_regs::TimedConfigIn9,
          usbdev_timed_regs::TimedConfigIn10, usbdev_timed_regs::TimedConfigIn11: begin
            // Prediction and checking of the `rdy` field may be disabled for a couple of sequences
            // because it is presently impractical to get the timing right for Isochronous IN
            // transactions.
            // Pending RTL changes in #23717, checking of `sending` is suppressed.
            include_field = (field_name != "rdy" || cfg.en_scb_rdchk_configin) &&
                             field_name != "sending";
            max_delay = 100;
          end
          // All other loosely-timed registers may be fully predicted.
          default: include_field = 1'b1;
        endcase
        if (include_field) begin
          // Extract the initial value of this register field from the modeled register state.
          uvm_reg_data_t mask = (1 << fields[f].get_n_bits()) - 1;
          init_val = (init_regs.r[r] >> fields[f].get_lsb_pos()) & mask;
          tr.add_field(fields[f], init_val, max_delay);
        end
        `uvm_info(`gfn, $sformatf("Register %p field %s : initially 0x%0x included %d", r,
                                  field_name, init_val, include_field), UVM_MEDIUM)
      end
      timed_regs.timed[r] = tr;
      if (r == r.last()) break;
      r = r.next();
    end
  endfunction

  function void capture_timed_regs(output bfm_timed_regs_t state);
    // Read FIFO level indicators.
    int unsigned avsetup_lvl = bfm.avsetup_fifo.size();
    int unsigned avout_lvl = bfm.avout_fifo.size();
    // Derive the 'full' status indicators from the levels.
    bit avsetup_full = (avsetup_lvl >= AvSetupFIFODepth);
    bit avout_full = (avout_lvl >= AvOutFIFODepth);
    int unsigned rx_lvl = bfm.rx_fifo.size();
    // RX FIFO Empty Status interrupt is asserted only when connection requested.
    bit rx_empty = bfm.enable & !rx_lvl;
    uvm_reg_data_t wake_events;
    uvm_reg_data_t usbstat;

    // DFM cannot reliably report the frame number or 'host_lost' indicator because it has no
    // time reference.
    usbstat = get_csr_val_with_updated_field(ral.usbstat.link_state, 0, bfm.link_state);
    usbstat = get_csr_val_with_updated_field(ral.usbstat.sense, usbstat, bfm.sense);
    usbstat = get_csr_val_with_updated_field(ral.usbstat.av_out_depth, usbstat, avout_lvl);
    usbstat = get_csr_val_with_updated_field(ral.usbstat.av_setup_depth, usbstat, avsetup_lvl);
    usbstat = get_csr_val_with_updated_field(ral.usbstat.av_out_full, usbstat, avout_full);
    usbstat = get_csr_val_with_updated_field(ral.usbstat.rx_depth, usbstat, rx_lvl);
    usbstat = get_csr_val_with_updated_field(ral.usbstat.av_setup_full, usbstat, avsetup_full);
    usbstat = get_csr_val_with_updated_field(ral.usbstat.rx_empty, usbstat, rx_empty);

    wake_events = get_csr_val_with_updated_field(ral.wake_events.module_active, 0,
                                                 bfm.wake_events.module_active);
    wake_events = get_csr_val_with_updated_field(ral.wake_events.disconnected, wake_events,
                                                 bfm.wake_events.disconnected);
    wake_events = get_csr_val_with_updated_field(ral.wake_events.bus_reset, wake_events,
                                                 bfm.wake_events.bus_reset);
    wake_events = get_csr_val_with_updated_field(ral.wake_events.bus_not_idle, wake_events,
                                                 bfm.wake_events.bus_not_idle);
    // Complete the register state.
    state.r[usbdev_timed_regs::TimedIntrState]  = bfm.intr_state | bfm.intr_test;
    state.r[usbdev_timed_regs::TimedUsbStat]    = usbstat;
    state.r[usbdev_timed_regs::TimedInSent]     = bfm.in_sent;
    state.r[usbdev_timed_regs::TimedWakeEvents] = wake_events;
    for (int unsigned ep = 0; ep < NEndpoints; ep++) begin
      uvm_reg_data_t configin;

      configin = get_csr_val_with_updated_field(ral.configin[ep].buffer, 0,
                                                bfm.configin[ep].buffer);
      configin = get_csr_val_with_updated_field(ral.configin[ep].size, configin,
                                                bfm.configin[ep].size);
      configin = get_csr_val_with_updated_field(ral.configin[ep].sending, configin,
                                                bfm.configin[ep].sending);
      configin = get_csr_val_with_updated_field(ral.configin[ep].pend, configin,
                                                bfm.configin[ep].pend);
      configin = get_csr_val_with_updated_field(ral.configin[ep].rdy, configin,
                                                bfm.configin[ep].rdy);
      state.r[usbdev_timed_regs::timed_reg_e'(usbdev_timed_regs::TimedConfigIn0 + ep)] = configin;
    end
  endfunction

  // Update the expectations for the timed registers; this should be called after any operation on
  // the BFM that could affect the state of one or more of the timed registers.
  function void update_timed_regs();
    usbdev_timed_regs::timed_reg_e r = r.first();
    bfm_timed_regs_t new_regs;
    capture_timed_regs(new_regs);
    forever begin
      // Has there been a change in the bits that we can predict?
      uvm_reg_data_t unpred_mask = timed_regs.timed[r].unpred_mask;
      if ((new_regs.r[r] & ~unpred_mask) != (prev_timed_regs.r[r] & ~unpred_mask)) begin
        timed_regs.predict(r, prev_timed_regs.r[r], new_regs.r[r]);
      end
      if (r == r.last()) break;
      r = r.next();
    end
    // Remember the register state.
    prev_timed_regs = new_regs;
  endfunction

  // These two tasks are overridden because the implementation in the base class performs checks
  // against predictions using its own memory model; instead, we choose to update the BFM packet
  // buffer memory within 'process_tl_addr' below, and then check the DUT read data against it in
  // 'process_tl_data' below.
  virtual task process_mem_write(tl_seq_item item, string ral_name);
  endtask
  virtual task process_mem_read(tl_seq_item item, string ral_name);
  endtask

  // Return the index that a register name refers to e.g. "configin_1" yields 1
  function int unsigned get_index_from_reg_name(string reg_name);
    int str_len = reg_name.len();
    // Note: this extracts the final two characters which are either '_y' or 'xy',
    //       and because '_' is permitted in (System)Verilog numbers, it works for 0-99
    string index_str = reg_name.substr(str_len-2, str_len-1);
    return index_str.atoi();
  endfunction

  // Look up the address of a TL access and return information about the target CSR (handle, name,
  // and index if it's within a bank of similar CSRs) or memory (name, word index within the
  // memory).
  function string lookup_tl_addr(ref tl_seq_item item, input string ral_name,
                                 output uvm_reg csr, output int unsigned index);
    // Attempt to locate a CSR at this address.
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      string csr_name;
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      csr_name = csr.get_name();
      index = get_index_from_reg_name(csr_name);
      return csr_name;
    end else if (is_mem_addr(item, ral_name)) begin
      // There is only a single memory window; it provides access to the packet buffer memory.
      uvm_mem mem = ral.default_map.get_mem_by_offset(item.a_addr);
      uvm_reg_addr_t masked_addr = item.a_addr & ral.get_addr_mask();
      uvm_reg_addr_t base;
      `DV_CHECK_NE(mem, null)
      base = mem.get_offset(0, ral.default_map);
      index = (masked_addr - base) >> $clog2(TL_DW / 8);
      // Caller shall use the name to differentiate from the CSRs.
      csr = null;
      return "buffer";
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access to unexpected addr 0x%0h", csr_addr))
    end
  endfunction

  // TL Address Channel transaction.
  function void process_tl_addr(ref tl_seq_item item, input string ral_name);
    logic [TL_DW-1:0] wdata = item.a_data;
    int unsigned index;
    uvm_reg csr;
    string csr_name = lookup_tl_addr(item, ral_name, csr, index);

    // Nothing to do here for reads.
    if (!item.is_write()) return;

    `uvm_info(`gfn, $sformatf("Writing 0x%0x to %s (index %0h)", wdata, csr_name, index),
              UVM_MEDIUM)
    if (csr_name != "buffer") void'(csr.predict(.value(wdata), .kind(UVM_PREDICT_WRITE)));

    // Update the state of the model according to this write operation.
    case (csr_name)
      // Interrupt handling.
      "intr_test": begin
        // `intr_test` just sets the `intr_state` bits for Event type interrupts; for Status type
        // interrupts it presents an additional stimulus alongside the status from the hardware.
        uvm_reg_data_t ro_mask = ral.intr_state.get_ro_mask();
        uvm_reg_data_t intr_state;
        bfm.intr_state |= wdata & IntrMask & ~ro_mask;
        bfm.intr_test = wdata & IntrMask & ro_mask;  // Stimulus for Status type interrupts.
        update_timed_regs();
        intr_state = bfm.intr_state | bfm.intr_test;
        // Sample tested interrupts.
        if (cfg.en_cov) begin
          foreach (wdata[i]) begin
            usbdev_intr_e intr = usbdev_intr_e'(i); // cast to enum to get interrupt name
            cov.intr_test_cg.sample(intr, wdata[i], bfm.intr_enable[i], intr_state[i]);
          end
        end
      end
      "intr_state": begin
        // Not all interrupt bits may be cleared; Status type interrupts must remain asserted in the
        // BFM.
        uvm_reg_data_t ro_mask = ral.intr_state.get_ro_mask();
        bfm.intr_state &= ~(wdata & IntrMask & ~ro_mask); // W1C
        `uvm_info(`gfn, $sformatf("intr_state after write 0x%0h is 0x%0h", wdata, bfm.intr_state),
                  UVM_MEDIUM)
        update_timed_regs();
      end
      "intr_enable": bfm.intr_enable = wdata & IntrMask;

      // Control register.
      "usbctrl": begin
        bfm.dev_address = get_field_val(ral.usbctrl.device_address, wdata);
        if (get_field_val(ral.usbctrl.resume_link_active, wdata)) bfm.resume_link_active();
        bfm.set_enable(get_field_val(ral.usbctrl.enable, wdata));
        update_timed_regs();
      end

      // Simple register configuration writes.
      "ep_out_enable":  bfm.ep_out_enable  = NEndpoints'(wdata);
      "ep_in_enable":   bfm.ep_in_enable   = NEndpoints'(wdata);
      "rxenable_setup": bfm.rxenable_setup = NEndpoints'(wdata);
      "rxenable_out":   bfm.rxenable_out   = NEndpoints'(wdata);
      "set_nak_out":    bfm.set_nak_out    = NEndpoints'(wdata);
      "out_stall":      bfm.out_stall      = NEndpoints'(wdata);
      "in_stall":       bfm.in_stall       = NEndpoints'(wdata);
      "out_iso":        bfm.out_iso        = NEndpoints'(wdata);
      "in_iso":         bfm.in_iso         = NEndpoints'(wdata);

      // configin_ registers (of which are there many), specifying IN packets for collection, are
      // more involved.
      $sformatf("configin_%0d", index): begin
        int unsigned ep = index;  // One register per endpoint.
        // Write 1 to clear fields.
        if (get_field_val(ral.configin[ep].sending, wdata)) bfm.configin[ep].sending = 1'b0;
        if (get_field_val(ral.configin[ep].pend, wdata))    bfm.configin[ep].pend    = 1'b0;
        bfm.configin[ep].buffer = get_field_val(ral.configin[ep].buffer, wdata);
        bfm.configin[ep].size   = get_field_val(ral.configin[ep].size,   wdata);
        bfm.configin[ep].rdy    = get_field_val(ral.configin[ep].rdy,    wdata);
        update_timed_regs();
      end

      // in_sent register, clears interrupts for sent packet.
      "in_sent": begin
        bfm.write_in_sent(wdata);
        update_timed_regs();
      end

      // Available Buffer FIFOs.
      "avoutbuffer": begin
        bfm.avout_fifo_add(get_field_val(ral.avoutbuffer.buffer, wdata));
        update_timed_regs();
      end
      "avsetupbuffer": begin
        bfm.avsetup_fifo_add(get_field_val(ral.avsetupbuffer.buffer, wdata));
        update_timed_regs();
      end

      "out_data_toggle": bfm.write_out_toggles(get_field_val(ral.out_data_toggle.mask,   wdata),
                                               get_field_val(ral.out_data_toggle.status, wdata));
      "in_data_toggle":  bfm.write_in_toggles(get_field_val(ral.in_data_toggle.mask,   wdata),
                                              get_field_val(ral.in_data_toggle.status, wdata));

      "fifo_ctrl": begin
        if (get_field_val(ral.fifo_ctrl.avout_rst, wdata))   bfm.avout_fifo_rst();
        if (get_field_val(ral.fifo_ctrl.avsetup_rst, wdata)) bfm.avsetup_fifo_rst();
        if (get_field_val(ral.fifo_ctrl.rx_rst, wdata))      bfm.rx_fifo_rst();
        update_timed_regs();
      end

      // Read Only registers.
      "usbstat",
      "rxfifo",
      "phy_pins_sense",
      "wake_events": begin
        `uvm_info(`gfn, $sformatf("Write to RO register '%0s'", csr_name), UVM_LOW)
      end

      // Wake control enables/disables AON/Wake functionality.
      "wake_control": begin
        bfm.set_wake_control(.suspend_req(get_field_val(ral.wake_control.suspend_req, wdata)),
                             .wake_ack(get_field_val(ral.wake_control.wake_ack, wdata)));
        update_timed_regs();
      end

      // Write Only registers that cannot be modified by the DUT hardware.
      "phy_config",
      "phy_pins_drive": begin
      end

      // Packet buffer access.
      "buffer": bfm.write_buffer(index, wdata);

      default: `uvm_fatal(`gfn, $sformatf("TL address access to '%0s' not handled", csr_name))
    endcase
  endfunction

  // TL Data Channel transaction.
  function void process_tl_data(ref tl_seq_item item, input string ral_name);
    logic [TL_DW-1:0] rdata = item.d_data;
    int unsigned index;
    uvm_reg csr;
    string csr_name = lookup_tl_addr(item, ral_name, csr, index);
    bit do_read_check = 1'b1;

    // Nothing to do here for writes.
    if (item.is_write()) return;

    `uvm_info(`gfn, $sformatf("Reading from %0s (index 0x%0h)", csr_name, index), UVM_MEDIUM)
    if (csr_name != "buffer") void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));

    case (csr_name)
      // Interrupt handling.
      "intr_state": begin
        uvm_reg_data_t intr_state = timed_regs.read(usbdev_timed_regs::TimedIntrState, rdata);
        `uvm_info(`gfn, $sformatf("intr_state read as 0x%0h", intr_state), UVM_MEDIUM)
        // Check that the interrupt state of the DUT matches that of the BFM.
        void'(csr.predict(.value(intr_state), .kind(UVM_PREDICT_READ)));
        // Sample asserted interrupt bits.
        if (cfg.en_cov) begin
          foreach (item.d_data[i]) begin
            usbdev_intr_e intr = usbdev_intr_e'(i); // cast to enum to get interrupt name
            cov.intr_cg.sample(intr, bfm.intr_enable[intr], item.d_data[intr]);
            cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
          end
        end
      end

      // The BFM has internal knowledge about the device address and enable, both of which may be
      // modified by the DUT in response to USB events.
      "usbctrl": begin
        uvm_reg_data_t usbctrl;
        usbctrl = get_csr_val_with_updated_field(ral.usbctrl.enable, 0, bfm.enable);
        usbctrl = get_csr_val_with_updated_field(ral.usbctrl.device_address, usbctrl,
                                                 bfm.dev_address);
        void'(csr.predict(.value(usbctrl), .kind(UVM_PREDICT_READ)));
      end

      "usbstat": begin
        // Note: we have a problem here that the BFM is faster at updating the status indications
        // than the DUT itself, since it takes the DUT a few cycles to propagate the changes through
        // prim_fifo_sync to the register interface.
        uvm_reg_data_t usbstat = timed_regs.read(usbdev_timed_regs::TimedUsbStat, rdata);
        void'(csr.predict(.value(usbstat), .kind(UVM_PREDICT_READ)));
      end

      // Simple register configuration reads; these registers are unmodified by the DUT hardware.
      "ep_out_enable",
      "ep_in_enable",
      "rxenable_setup",
      "set_nak_out",
      "out_stall",
      "in_stall",
      "out_iso",
      "in_iso": do_read_check = 1'b1;

      // In response to OUT traffic, the `rxenable_out` bit may be changed by the 'set_nak_out'
      // software-managed gating of OUT packets to the endpoint.
      "rxenable_out": begin
        void'(csr.predict(.value(bfm.rxenable_out), .kind(UVM_PREDICT_READ)));
      end

      "avoutbuffer",
      "avsetupbuffer": begin
        `uvm_fatal(`gfn, "Should never be attempting to read from Av Buffer FIFO")
      end

      "rxfifo": begin
        // Collect a RX FIFO entry from the BFM, if there is one.
        usbdev_bfm::rxfifo_entry_t entry;
        if (bfm.rx_fifo_read(entry)) begin
          // Check the fields of the RX FIFO match the expectations produced by the BFM.
          `DV_CHECK_EQ(get_field_val(ral.rxfifo.buffer, rdata), entry.buffer, "RX buffer mismatch")
          `DV_CHECK_EQ(get_field_val(ral.rxfifo.ep,     rdata), entry.ep,     "RX ep mismatch")
          `DV_CHECK_EQ(get_field_val(ral.rxfifo.setup,  rdata), entry.setup,  "RX setup mismatch")
          `DV_CHECK_EQ(get_field_val(ral.rxfifo.size,   rdata), entry.size,   "RX size mismatch")
          // Reading from the RX FIFO may cause changes to both `intr_state` and `usbstat`.
          update_timed_regs();
        end else begin
          // Note: DV should never really be doing this; but the DUT won't fault it.
          `uvm_fatal(`gfn, "Should never be attempting to read from RX FIFO when empty")
        end
      end

      // configin_ registers (of which are there many), specifying IN packets for collection.
      // Note: the BFM has its own idea of these registers, but there is a further complication of
      // the hardware-modified status bits 'sending' and 'pend' being timing-dependent.
      $sformatf("configin_%0d", index): begin
        usbdev_timed_regs::timed_reg_e r;
        uvm_reg_data_t configin;
        r = usbdev_timed_regs::timed_reg_e'(usbdev_timed_regs::TimedConfigIn0 + index);
        configin = timed_regs.read(r, rdata);
        void'(csr.predict(.value(configin), .kind(UVM_PREDICT_READ)));
      end

      // The BFM internal state will be modified by collection of IN packets.
      "in_sent": begin
        uvm_reg_data_t in_sent = timed_regs.read(usbdev_timed_regs::TimedInSent, rdata);
        void'(csr.predict(.value(in_sent), .kind(UVM_PREDICT_READ)));
      end

      // The BFM has internal knowledge of the Data Toggle bits because packet transactions
      // and link resets modify them.
      "out_data_toggle": void'(csr.predict(.value(bfm.out_toggles), .kind(UVM_PREDICT_READ)));
      "in_data_toggle":  void'(csr.predict(.value(bfm.in_toggles),  .kind(UVM_PREDICT_READ)));

      // The BFM makes no attempt to provide full pin-level information, but IF pin driving is
      // enabled we can form a prediction using what the RAL knows about the register
      // `phy_pins_drive`.
      "phy_pins_sense": begin
        // We can only form predictions if the pins are under register control, but some sequences
        // read from this register without using pin driving.
        if (`gmv(ral.phy_pins_drive.en)) begin
          // Collect signals `from phy_pins_drive`.
          bit dn_pullup_en_o = `gmv(ral.phy_pins_drive.dn_pullup_en_o);
          bit dp_pullup_en_o = `gmv(ral.phy_pins_drive.dp_pullup_en_o);
          bit rx_enable_o = `gmv(ral.phy_pins_drive.rx_enable_o);
          bit oe_o  = `gmv(ral.phy_pins_drive.oe_o);
          bit dn_o  = `gmv(ral.phy_pins_drive.dn_o);
          bit dp_o  = `gmv(ral.phy_pins_drive.dp_o);
          // Assume that the bus is undriven by the host/agent, and that the DUT or the pullup have
          // control of the bus. If neither has, the weak pulldown resistors of the host define the
          // signal state.
          bit rx_dp_i = oe_o ? dp_o : dp_pullup_en_o;
          bit rx_dn_i = oe_o ? dn_o : dn_pullup_en_o;
          bit rx_d_i  = rx_enable_o ? (rx_dp_i & ~rx_dn_i) : 1'b0;
          uvm_reg_data_t sense;
          // The BFM _does_ know about the VBUS/SENSE connection.
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.pwr_sense, 0, bfm.sense);
          // The transmitter is expected to be Idle, but not driving the USB.
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.tx_oe_o,  sense, 1'b0);
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.tx_se0_o, sense, 1'b0);
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.tx_d_o,   sense, 1'b1);
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.tx_dn_o,  sense, 1'b0);
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.tx_dp_o,  sense, 1'b1);
          // The receiver should observe the USB as driven by the register state.
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.rx_d_i,   sense, rx_d_i);
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.rx_dn_i,  sense, rx_dn_i);
          sense = get_csr_val_with_updated_field(ral.phy_pins_sense.rx_dp_i,  sense, rx_dp_i);
          void'(csr.predict(.value(sense), .kind(UVM_PREDICT_READ)));
        end else do_read_check = 1'b0;
      end

      // The BFM has internal knowledge of the USB events occurring during AON/Wake activation.
      "wake_events": begin
        uvm_reg_data_t wake_events = timed_regs.read(usbdev_timed_regs::TimedWakeEvents, rdata);
        void'(csr.predict(.value(wake_events), .kind(UVM_PREDICT_READ)));
      end

      // These counters are development/diagnostic aids only; they are not modeled in the BFM.
      "count_out",
      "count_in",
      "count_nodata_in",
      "count_errors": do_read_check = 1'b0;

      // Write Only registers that cannot be altered by the DUT hardware.
      "intr_test",
      "intr_enable",
      "alert_test",
      "wake_control",
      "phy_config",
      "phy_pins_drive",
      "fifo_ctrl": begin
        // Nothing to do; use RAL prediction.
      end

      // Packet buffer access.
      "buffer": begin
        // Check read data from the DUT against BFM packet buffer contents.
        logic [TL_DW-1:0] exp_data = bfm.read_buffer(index);
        `DV_CHECK_EQ(item.d_data, exp_data, "Unexpected read data from packet buffer memory")
        // Do not attempt to access/check 'csr' below.
        do_read_check = 1'b0;
      end

      default: `uvm_fatal(`gfn, $sformatf("TL data access to '%0s' not handled", csr_name))
    endcase
    // On reads, if do_read_check is set, check the returned read data against the  mirrored value.
    if (do_read_check) begin
      `DV_CHECK_EQ(item.d_data, csr.get_mirrored_value(),
                   $sformatf("CSR read data mismatches prediction (%0s)", csr.get_full_name()))
    end
    if (csr_name != "buffer") void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    case (channel)
      AddrChannel: process_tl_addr(item, ral_name);
      DataChannel: process_tl_data(item, ral_name);
      default: `uvm_fatal(`gfn, $sformatf("Invalid channel: %0h", channel))
    endcase
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // Reset local fifos queues and variables
    req_usb20_fifo.flush();
    rsp_usb20_fifo.flush();
    expected_rsp_q.delete();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // Post test checks to ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(usb20_item, req_usb20_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(usb20_item, rsp_usb20_fifo)
  endfunction

endclass
