// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_dpi_config_host_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_dpi_config_host_vseq)

  `uvm_object_new

  // State within the present Control Transfer
  typedef enum {
    // Awaiting receipt of SETUP stage
    Ctl_AwaitSETUP,
    // Awaiting Status Stage
    Ctl_AwaitStatus
  } ctl_state_e;

  // Current Control Transfer
  typedef enum {
    Cfg_DescDev,
    Cfg_DescCfg,
    Cfg_DescTest
  } cfg_state_e;

  // Control Transfers thus far completed.
  bit desc_dev_done  = 1'b0;  // GET_DESCRIPTOR for Device
  bit desc_cfg_done  = 1'b0;  // GET_DESCRIPTOR for Configuration
  bit addr_set_done  = 1'b0;  // SET_ADDRESS
  bit cfg_set_done   = 1'b0;  // SET_CONFIG
  bit desc_test_done = 1'b0;  // GET_DESCRIPTOR for vendor-specific test descriptor

  // We use these ranges of buffers for reception at start up, just returning any received buffer
  // immediately.
  bit [4:0] setup_buf_first = 0;
  bit [4:0] setup_buf_last  = 2;
  bit [4:0] out_buf_first   = 8;
  bit [4:0] out_buf_last    = 12;

  // Buffer number used for transmission
  bit [4:0] in_buf = 19;

  // Device descriptor
  byte unsigned desc_device[] = {
    // Our standard device descriptor; see sw/device/lib/testing/usb_testutils_controlep.c
    1, 0, 0, 0, 1, 0, 8'h50, 8'h3a, 8'h18, 8'hd1, 64, 0, 0, 0, 2, 0, 1, 18
  };

  // Configuration descriptor; may be completed by derivative sequences.
  byte unsigned desc_config[];

  // Test descriptor; may be completed by derivative sequences.
  byte unsigned desc_test[];

  // ACKnowledge packet (Status stage, so this is just a zero-length packet).
  byte unsigned ack[];

  virtual task pre_start();
    // First of all we want to ensure that the DPI model is connected via the 'usb20_if' which
    // models a physical USB, rather than employing the block-level DV interface.
    cfg.m_usb20_agent_cfg.bif.enable_driver(1'b0);
    cfg.usb20_usbdpi_vif.enable_driver(1'b1);

    // We want full control of the DUT configuration and communications with the DPI model.
    do_agent_connect = 1'b0;
    do_usbdev_init = 1'b0;
    super.pre_start();
  endtask

  // Test for and receive a packet from the host.
  virtual task packet_recv(output bit rx_pending, output bit rx_setup,
                           output byte unsigned rx_data[]);
    uvm_reg_data_t data;
    rx_pending = 0;
    csr_rd(.ptr(ral.intr_state), .value(data));
    if (get_field_val(ral.intr_state.pkt_received, data)) begin
      int unsigned rx_buf;
      int unsigned rx_len;
      csr_rd(.ptr(ral.rxfifo), .value(data));
      rx_buf   = get_field_val(ral.rxfifo.buffer, data);
      rx_len   = get_field_val(ral.rxfifo.size,   data);
      rx_setup = get_field_val(ral.rxfifo.setup,  data);
      read_buffer(rx_buf, rx_len, rx_data);
      // Return the buffer to the appropriate Available Buffer FIFO.
      if (rx_setup) begin
        // SETUP packets used the Av SETUP FIFO.
        csr_wr(.ptr(ral.avsetupbuffer.buffer), .value(rx_buf));
      end else begin
        // OUT packets used the Av OUT FIFO.
        csr_wr(.ptr(ral.avoutbuffer.buffer), .value(rx_buf));
      end
      // Successfully read and returned a packet.
      rx_pending = 1;
    end
  endtask

  // Send a packet to the host, await response and check ACK handshake indicating reception.
  virtual task packet_send(byte unsigned tx_data[]);
    int timeout_clks = 1_000_000;
    uvm_reg_data_t in_sent;
    bit pkt_sent;
    write_buffer(in_buf, tx_data);
    // Present the IN packet for collection.
    ral.configin[0].size.set(tx_data.size());
    ral.configin[0].buffer.set(in_buf);
    ral.configin[0].rdy.set(1'b0);
    csr_update(ral.configin[0]);
    // Now set the RDY bit
    ral.configin[0].rdy.set(1'b1);
    csr_update(ral.configin[0]);
    // Wait until the packet is successfully retrieved and ACKed by the host.
    do begin
      uvm_reg_data_t intr_state;
      timeout_clks -= 128;
      cfg.clk_rst_vif.wait_clks(128);
      csr_rd(ral.intr_state, intr_state);
      pkt_sent = bit'(get_field_val(ral.intr_state.pkt_sent, intr_state));
    end while (!pkt_sent && timeout_clks > 0);
    `DV_CHECK_EQ(pkt_sent, 1, "IN packet not successfully collected by DPI model");
    // Clear the SENT interrupt for all endpoints; should be just EP 0.
    csr_rd(.ptr(ral.in_sent[0]), .value(in_sent));
    csr_wr(.ptr(ral.in_sent[0]), .value(in_sent));
  endtask

  // Dump out the contents of a packet.
  virtual function void packet_dump(byte unsigned pkt[]);
    for (int unsigned i = 0; i < pkt.size(); i++) begin
      `uvm_info(`gfn, $sformatf("%2d: 0x%02x", i, pkt[i]), UVM_MEDIUM)
    end
  endfunction

  // Present a range of buffer IDs for use by SETUP packets.
  virtual task setup_buffers_supply(int unsigned first, int unsigned last);
    for (int unsigned bufnum = first; bufnum <= last; bufnum++) begin
      csr_wr(.ptr(ral.avsetupbuffer.buffer), .value(bufnum));
    end
  endtask

  // Present a range of buffer IDs for use by OUT packets.
  virtual task out_buffers_supply(int unsigned first, int unsigned last);
    for (int unsigned bufnum = first; bufnum <= last; bufnum++) begin
      csr_wr(.ptr(ral.avoutbuffer.buffer), .value(bufnum));
    end
  endtask

  // Set up the control endpoint to implement the Default Control Pipe
  virtual task endpoint_ctl_setup();
    csr_wr(.ptr(ral.ep_out_enable[0]),  .value(1));
    csr_wr(.ptr(ral.ep_in_enable[0]),   .value(1));
    csr_wr(.ptr(ral.rxenable_setup[0]), .value(1));
    csr_wr(.ptr(ral.rxenable_out[0]),   .value(1));
  endtask

  // Wait until the DPI host has issued the normal Control Transfers to set the
  // device configuration.
  virtual task configuration_wait();
    import usb_consts_pkg::*;

    ctl_state_e ctl_state = Ctl_AwaitSETUP;
    cfg_state_e cfg_state = Cfg_DescDev;

    // Respond to standard Control Transfers until SET_CONFIG received
    //
    // Accept GET_DESCRIPTOR for Device, SET_ADDRESS and GET_DESCRIPTOR for
    // configuration(s) in any order, before SET_CONFIG which we require but
    // essentially ignore.
    //
    // If these all occur then we may regard the device as having been successfully
    // configured by the USB host.
    while (~&{desc_dev_done, addr_set_done, desc_cfg_done, cfg_set_done}) begin
      byte unsigned rx_data[];
      int unsigned rx_len;
      bit rx_pending;
      bit rx_setup;
      // Await appropriate stimulus
      case (ctl_state)
        Ctl_AwaitSETUP: begin
          // Collect SETUP DATA packet and decode
          packet_recv(rx_pending, rx_setup, rx_data);
          if (rx_pending) begin
            `DV_CHECK(rx_setup && rx_data.size() == 8)
            packet_dump(rx_data);
            casez ({rx_data[1], rx_data[3]})
              {SetupSetAddress, 8'h00}: begin
                // USB device addresses are 7 bits.
                byte unsigned dev_address = rx_data[2] & 8'h7f;
                `uvm_info(`gfn, $sformatf("SET_ADDRESS %d received", dev_address), UVM_LOW)
                packet_send(ack);
                csr_wr(.ptr(ral.usbctrl.device_address), .value(dev_address));
                addr_set_done = 1;
              end
              {SetupGetDescriptor, 8'h01}: begin
                `uvm_info(`gfn, $sformatf("GET_DESCRIPTOR DEVICE"), UVM_LOW)
                packet_send(desc_device);
                ctl_state = Ctl_AwaitStatus;
                cfg_state = Cfg_DescDev;
              end
              {SetupGetDescriptor, 8'h02}: begin
                `uvm_info(`gfn, $sformatf("GET_DESCRIPTOR CONFIG"), UVM_LOW)
                packet_send(desc_config);
                ctl_state = Ctl_AwaitStatus;
                cfg_state = Cfg_DescCfg;
              end
              {SetupSetConfiguration, 8'h00}: begin
                `uvm_info(`gfn, $sformatf("SET_CONFIGURATION"), UVM_LOW)
                packet_send(ack);
                cfg_set_done = 1;
              end
              // TODO: we do not handle this vendor-specific Control Transfer at present,
              // but we may do later for requesting fault injection testing etc.
              default: begin
                `uvm_info(`gfn, $sformatf("GET_DESCRIPTOR TEST"), UVM_LOW)
                packet_send(desc_test);
                ctl_state = Ctl_AwaitStatus;
                cfg_state = Cfg_DescTest;
              end
            endcase
          end
        end
        Ctl_AwaitStatus: begin
          packet_recv(rx_pending, rx_setup, rx_data);
          if (rx_pending) begin
            `DV_CHECK(!rx_setup && !rx_data.size())
            // Control Transfer complete
            case (cfg_state)
              Cfg_DescDev: begin
                desc_dev_done = 1;
                ctl_state = Ctl_AwaitSETUP;
              end
              Cfg_DescCfg: begin
                desc_cfg_done = 1;
                ctl_state = Ctl_AwaitSETUP;
              end
              default: begin
                desc_test_done = 1;
                ctl_state = Ctl_AwaitSETUP;
              end
            endcase
          end
        end
        default: `uvm_fatal(`gfn, $sformatf("Invalid/unrecognised state %d", ctl_state))
      endcase
    end
  endtask

  virtual task body();
    // Default Control Pipe configuration.
    endpoint_ctl_setup();

    // Populate Av FIFOs.
    setup_buffers_supply(setup_buf_first, setup_buf_last);
    out_buffers_supply(out_buf_first, out_buf_last);

    // Enable interface
    csr_wr(.ptr(ral.usbctrl.enable), .value(1));

    // Wait for the normal device configuration sequence to complete.
    configuration_wait();

    // At this point the configuration sequence has completed.
    `uvm_info(`gfn, $sformatf("Configuration completed"), UVM_MEDIUM)
  endtask

endclass
