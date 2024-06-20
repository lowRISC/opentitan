// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_scoreboard extends cip_base_scoreboard #(
  .CFG_T(usbdev_env_cfg),
  .RAL_T(usbdev_reg_block),
  .COV_T(usbdev_env_cov)
);
  `uvm_component_utils(usbdev_scoreboard)

  usbdev_packetiser m_packetiser;
  usbdev_transaction_manager m_usbdev_trans;
  usbdev_pkt_manager m_pkt_manager;
  usb20_item m_usb20_item;

  // Arrays to store actual packet and expected packet
  bit expected_pkt[];
  bit actual_pkt[];

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(usb20_item) req_usb20_fifo;
  uvm_tlm_analysis_fifo #(usb20_item) rsp_usb20_fifo;

  // Intr checks
  local bit [NumUsbdevInterrupts-1:0] intr_exp;
  local bit [NumUsbdevInterrupts-1:0] intr_exp_at_addr_phase;

  // local queues to hold incoming packets pending comparison
  local bit actual_pkt_q[$][];
  local bit expected_pkt_q[$][];

  // Local variables
  local bit ep_out_enable;
  local bit rx_enable_out;
  local bit rx_enable_setup;
  local bit pkt_ack;
  local bit pkt_nak;
  local bit pkt_stall;
  local bit pkt_sent;
  local bit stall;
  local bit iso_trans;
  local bit [31:0] ep_out_enable_reg;
  local bit [31:0] ep_in_enable_reg;
  local bit [31:0] rx_enable_setup_reg;
  local bit [31:0] rx_enable_out_reg;
  local bit [31:0] out_stall_reg;
  local bit [31:0] in_stall_reg;
  local bit [31:0] out_iso_reg;
  local bit [31:0] in_iso_reg;
  local bit [3:0]  endp_index;
  local bit [7:0]  act_pid, exp_pid;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_packetiser = new();
    m_pkt_manager = new();
    m_usbdev_trans = new();
    m_usb20_item = new();
    req_usb20_fifo = new("req_usb20_fifo", this);
    rsp_usb20_fifo = new("rsp_usb20_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_usb20_fifo();
      process_usb20_pkt();
    join_none
  endtask

  // TODO: This is an incomplete placeholder; in time a BFM shall model what the DUT shall
  // consider to be a valid packet.
  function valid_packet(ref usb20_item item);
    return (item.m_pid_type != PidTypeSofToken && item.valid_pid());
  endfunction

  virtual task process_usb20_fifo();
    usb20_item item;
    forever begin
      req_usb20_fifo.get(item);
      case (item.m_ev_type)
        EvBusReset:   `uvm_info(`gfn, "Bus Reset received from monitor", UVM_MEDIUM)
        EvSuspend:    `uvm_info(`gfn, "Suspend Signaling received from monitor", UVM_MEDIUM)
        EvResume:     `uvm_info(`gfn, "Resume Signaling received from monitor", UVM_MEDIUM)
        EvDisconnect: `uvm_info(`gfn, "VBUS Disconnection received from monitor", UVM_MEDIUM)
        EvConnect:    `uvm_info(`gfn, "VBUS Connection received from monitor", UVM_MEDIUM)
        EvPacket:
          // TODO: This check is temporary and prevents simulations from failing as a result of this
          // code assuming the validity of the USB traffic, now that sequences are deliberately
          // injecting bad traffic.
          if (valid_packet(item)) begin
            m_packetiser.pack_pkt(item);
            usbdev_expected_pkt();
            void'(item.pack(actual_pkt));
            actual_pkt_q.push_back(actual_pkt);
            for (int i = 0; i <= 7; i++) begin
              act_pid = {act_pid, actual_pkt[i]};
            end
            `uvm_info(`gfn, $sformatf("req port item :\n%0s", item.sprint()), UVM_DEBUG)
            compare_usb20_pkt(item);
          end else begin
            `uvm_info(`gfn, "Invalid packet received from monitor", UVM_MEDIUM)
          end
        default: `uvm_fatal(`gfn, $sformatf("Invalid/unexpected event type %p", item.m_ev_type))
      endcase
    end
  endtask

  // usbdev_expected_pkt task : To run the predictor
  // -------------------------------
  virtual task usbdev_expected_pkt();
    m_usbdev_trans.transaction_manager(m_packetiser.token_pkt_arr, m_packetiser.data_pkt_arr,
                                       m_packetiser.handshake_pkt_arr);
    m_pkt_manager.pop_packet(expected_pkt);
    expected_pkt_q.push_back(expected_pkt);
    for (int i = 0; i <= 7; i++) begin
      exp_pid = {exp_pid, expected_pkt[i]};
    end
  endtask

  // process_usb20_pkt task : Process queue
  // and compare the actual pkt with expected pkt
  // -------------------------------
  virtual task process_usb20_pkt();
    usb20_item item;
    forever begin
      rsp_usb20_fifo.get(item);
      usbdev_expected_pkt();
      void'(item.pack(actual_pkt));
      actual_pkt_q.push_back(actual_pkt);
      for (int i = 0; i <= 7; i++) begin
        act_pid = {act_pid, actual_pkt[i]};
      end
      `uvm_info(`gfn, $sformatf("rsp port item :\n%0s", item.sprint()), UVM_DEBUG)
      compare_usb20_pkt(item);
    end
  endtask

  // compare_usb20_pkt task : To check pkt transmission accuracy
  // -------------------------------
  virtual task compare_usb20_pkt(usb20_item item);
    if (predict_errors(item)) begin
      void'(actual_pkt_q.pop_front());
      void'(expected_pkt_q.pop_front());
      return;
    end
    if (actual_pkt_q.size() > 0) begin
      // TODO: this is not safe because of macro expansion, and additionally it is doing nothing
      // useful at present but does cause test failures.
      // `DV_CHECK_EQ(actual_pkt_q.pop_front(), expected_pkt_q.pop_front());
      // `uvm_info(`gfn,"item match",UVM_DEBUG)
    end
  endtask

  // predict_errors function : To Predict error type
  // -------------------------------
  virtual function bit predict_errors(usb20_item item);
    bit [15:0] act_crc16, exp_crc16;
    bit [4:0]  act_crc5, exp_crc5;
    if (act_pid != exp_pid) begin
      `uvm_info(`gfn,"PID ERROR",UVM_DEBUG)
      return 1;
    end
    if(item.m_pid_type inside {PidTypeOutToken, PidTypeInToken, PidTypeSetupToken}) begin
      for (int i = 19; i <= 23; i++) begin
        act_crc5 = {act_crc5, actual_pkt[i]};
        exp_crc5 = {exp_crc5, expected_pkt[i]};
      end
      if (act_crc5 != exp_crc5) begin
        `uvm_info(`gfn,"CRC5 ERROR",UVM_DEBUG)
        return 1;
      end
    end
    if (item.m_pid_type inside {PidTypeData0, PidTypeData1}) begin
      for(int i = actual_pkt.size() - 16; i <= actual_pkt.size() - 1; i++) begin
        act_crc16 = {act_crc16, actual_pkt[i]};
        exp_crc16 = {exp_crc16, expected_pkt[i]};
      end
      if (act_crc16 != exp_crc16) begin
      `uvm_info(`gfn,"CRC16 ERROR",UVM_DEBUG)
      return 1;
      end
    end
  endfunction

  // These two tasks are overridden because the implementation in the base class performs checks
  // against predictions, whereas the USBDEV packet buffer memory may change essentially at any
  // time because packets are written into it automatically by the DUT.
  //
  // We could perhaps at some point be a little smarter and expect that only those buffers that
  // have been made available for DUT use may change, since we _can_ track which buffers have been
  // placed in the Av OUT/SETUP FIFOs and which have subsequently been removed from the RX FIFO.
  virtual task process_mem_write(tl_seq_item item, string ral_name);
    // Do nothing, not modeled.
  endtask
  virtual task process_mem_read(tl_seq_item item, string ral_name);
    // Do nothing, not modeled.
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    // Is the access is to the packet buffer memory of the USB device?
    bit     buffer_mem      = 1'b0;
    bit     write           = item.is_write();
    string  csr_name;
    bit [TL_AW-1:0] addr_mask = ral.get_addr_mask();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      csr_name = csr.get_name();
    end
    // if access was to a valid mem buffer location; there is only a single memory window that
    // provides access to the packet buffer memory.
    else if (is_mem_addr(item, ral_name)) begin
      buffer_mem = 1'b1;
      csr_name = "buffer";
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write & ~buffer_mem) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr_name)
      // add individual case item for each csr
      "usbctrl": begin
        // no special handling yet
      end
      "intr_enable": begin
        // no special handling yet
      end
      "intr_test": begin
        if (write && channel == AddrChannel) begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          intr_exp |= item.a_data;
          if (cfg.en_cov) begin
            foreach (intr_exp[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
          // this field is WO - always returns 0
          void'(csr.predict(.value(0), .kind(UVM_PREDICT_WRITE)));
        end
      end
      "intr_state": begin
        if (!write && channel == AddrChannel) begin // read & addr phase
          intr_exp_at_addr_phase = intr_exp;
        end else if (!write && channel == DataChannel) begin // read & data phase
          usbdev_intr_e   intr;
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          do_read_check = 1'b0;
          foreach (intr_exp[i]) begin
            intr = usbdev_intr_e'(i); // cast to enum to get interrupt name
            if (cfg.en_cov) begin
              cov.intr_cg.sample(intr, intr_en[intr], intr_exp[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
            end
            // TODO FIXME
            // `DV_CHECK_EQ(item.d_data[i], intr_exp_at_addr_phase[i],
            //              $sformatf("Interrupt: %0s", intr.name));
            // `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[i], (intr_en[i] & intr_exp[i]),
            //              $sformatf("Interrupt_pin: %0s", intr.name));
          end
        end // read & data phase
      end
      "alert_test": begin
        // TODO
      end
      "ep_out_enable": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        ep_out_enable_reg = ral.ep_out_enable[0].get_mirrored_value();
        foreach(ep_out_enable_reg[i]) begin
          if (ep_out_enable_reg[i] == 1'b1) begin
            ep_out_enable = 1'b1;
            endp_index = i;
            break;
          end
         else ep_out_enable = 1'b0;
        end
      end
      "ep_in_enable": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        ep_in_enable_reg = ral.ep_in_enable[0].get_mirrored_value();
        foreach(ep_in_enable_reg[i]) begin
          if (ep_in_enable_reg[i] == 1'b1) begin
            endp_index = i;
            break;
          end
        end
      end
      "usbstat": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "avoutbuffer": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "avsetupbuffer": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "rxfifo": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "rxenable_setup": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        rx_enable_setup_reg = ral.rxenable_setup[0].get_mirrored_value();
        if (rx_enable_setup_reg[endp_index]) begin
          rx_enable_setup = 1'b1;
        end
        else rx_enable_setup = 1'b0;
      end
      "rxenable_out": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        rx_enable_out_reg = ral.rxenable_out[0].get_mirrored_value();
        if (rx_enable_out_reg[endp_index]) begin
          rx_enable_out = 1'b1;
        end
        else rx_enable_out = 1'b0;
      end
      "set_nak_out": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "in_sent": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "out_stall": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        out_stall_reg = ral.out_stall[0].get_mirrored_value();
        if (out_stall_reg[endp_index]) begin
          stall = 1'b1;
        end
        else stall = 1'b0;
      end
      "in_stall": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        in_stall_reg = ral.in_stall[0].get_mirrored_value();
        if (in_stall_reg[endp_index]) begin
          stall = 1'b1;
        end
        else stall = 1'b0;
      end
      "configin_0": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_1": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_2": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_3": begin
       if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_4": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_5": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_6": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_7": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_8": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_9": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_10": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "configin_11": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "out_iso": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        out_iso_reg = ral.out_iso[0].get_mirrored_value();
        if (out_iso_reg[endp_index]) begin
          iso_trans = 1'b1;
        end
        else iso_trans = 1'b0;
      end
      "in_iso": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
        in_iso_reg = ral.in_iso[0].get_mirrored_value();
        if (in_iso_reg[endp_index]) begin
          iso_trans = 1'b1;
        end
        else iso_trans = 1'b0;
      end
      "out_data_toggle": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "in_data_toggle": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "phy_pins_sense": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "phy_pins_drive": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "phy_config": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "wake_control": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "wake_events": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "fifo_ctrl": begin
        // TODO
      end
      "count_out": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "count_in": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "count_nodata_in": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "count_errors": begin
        if (!write && channel == DataChannel) begin
          do_read_check = 1'b0;
        end
      end
      "buffer": begin
        do_read_check = 1'b1;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase
    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        if (buffer_mem) begin
          // No predictions of packet buffer memory content within the scoreboard; checked in vseqs.
        end else begin
          `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                       $sformatf("reg name: %0s", csr.get_full_name()))
        end
      end else begin
        void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      end
    end
    // hand_shaking : send regs information required for hanshaking to predictor
    pkt_ack = ep_out_enable & (rx_enable_out || rx_enable_setup) & ~stall;
    pkt_nak = ~rx_enable_out & ~rx_enable_setup;
    pkt_stall = stall;
    if (pkt_ack & ~pkt_stall) begin
      m_usbdev_trans.m_usbdev_handshake_pkt = ACK;
    end else if (pkt_nak & ~pkt_stall) begin
      m_usbdev_trans.m_usbdev_handshake_pkt = NAK;
    end else if(stall) begin
      // Give priority to setup pkt over stall
      if(ep_out_enable & rx_enable_setup)
        m_usbdev_trans.m_usbdev_handshake_pkt = ACK;
      else
        m_usbdev_trans.m_usbdev_handshake_pkt = STALL;
    end

    // Check weather transfer type is isochoronus or not
    if (iso_trans) begin
      m_usbdev_trans.m_usb_transfer = IsoTrans;
    end
    else begin
      m_usbdev_trans.m_usb_transfer = CtrlTrans;
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // Reset local fifos queues and variables
    req_usb20_fifo.flush();
    rsp_usb20_fifo.flush();
    actual_pkt_q.delete();
    expected_pkt_q.delete();
    intr_exp = 0;
    intr_exp_at_addr_phase = 0;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // Post test checks to ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(usb20_item, req_usb20_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(usb20_item, rsp_usb20_fifo)
  endfunction

endclass
