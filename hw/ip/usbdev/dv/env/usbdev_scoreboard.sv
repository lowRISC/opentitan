// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_scoreboard extends cip_base_scoreboard #(
  .CFG_T(usbdev_env_cfg),
  .RAL_T(usbdev_reg_block),
  .COV_T(usbdev_env_cov)
);
  `uvm_component_utils(usbdev_scoreboard)

  usbdev_packetiser  m_packetiser;
  usbdev_TransactionManager m_usbdev_trans;
  usbdev_pkt_manager m_pkt_manager;
  usb20_item m_usb20_item;

  // Arrays to store actual packet and expected packet
  bit expected_pkt[];
  bit actual_pkt[];

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(usb20_item) usb20_fifo;

  // Intr checks
  local bit [NumUsbdevInterrupts-1:0] intr_exp;
  local bit [NumUsbdevInterrupts-1:0] intr_exp_at_addr_phase;

  // local queues to hold incoming packets pending comparison
  usb20_item usb20_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_packetiser = new();
    m_pkt_manager = new();
    m_usbdev_trans = new();
    m_usb20_item = new();
    usb20_fifo = new("usb20_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_usb20_fifo();
    join_none
  endtask

  virtual task process_usb20_fifo();
    usb20_item item;
    forever begin
      usbdev_expected_pkt();
      usb20_fifo.get(item);
      item.pack(actual_pkt);
      `uvm_info(`gfn, $sformatf("received usb20 item :\n%0s", item.sprint()), UVM_DEBUG)
      `uvm_info(`gfn, $sformatf("ACTUAL PACKET : %p", actual_pkt), UVM_DEBUG)
    end
  endtask

  // usbdev_expected_pkt task : To run the predictor
  // and compare the actual pkt with expected pkt
  // -------------------------------
  virtual task usbdev_expected_pkt();
    m_packetiser.pack_pkt(m_usb20_item);
    m_usbdev_trans.transaction_manager(m_packetiser.token_pkt_arr, m_packetiser.data_pkt_arr,
                                       m_packetiser.handshake_pkt_arr);
    m_pkt_manager.pop_packet(expected_pkt);
    `uvm_info(`gfn, $sformatf("EXPECTED PACKET : %p", expected_pkt), UVM_DEBUG)
    foreach(actual_pkt[i])
      `DV_CHECK_EQ(actual_pkt[i], expected_pkt[i]);
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase

    case (csr.get_name())
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
        // TODO
      end
      "ep_in_enable": begin
        // TODO
      end
      "usbstat": begin
        do_read_check = 1'b0;
      end
      "avbuffer": begin
        // TODO
      end
      "rxfifo": begin
        do_read_check = 1'b0;
      end
      "rxenable_setup": begin
        // TODO
      end
      "rxenable_out": begin
        // TODO
      end
      "set_nak_out": begin
        // TODO
      end
      "in_sent": begin
        // TODO
      end
      "out_stall": begin
        // TODO
      end
      "in_stall": begin
        // TODO
      end
      "configin": begin
        // TODO
      end
      "out_iso": begin
        // TODO
      end
      "in_iso": begin
        // TODO
      end
      "data_toggle_clear": begin
        // TODO
      end
      "phy_pins_sense": begin
        // TODO
      end
      "phy_pin_drive": begin
        // TODO
      end
      "phy_config": begin
        // TODO
      end
      "wake_control": begin
        // TODO
      end
      "wake_events": begin
        // TODO
      end
      "buffer": begin
        // TODO
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // Reset local fifos queues and variables
    usb20_fifo.flush();
    usb20_q.delete();
    intr_exp = 0;
    intr_exp_at_addr_phase = 0;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // Post test checks to ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(usb20_item, usb20_fifo)
    `DV_EOT_PRINT_Q_CONTENTS(usb20_item, usb20_q)
  endfunction

endclass
