// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_base_vseq extends cip_base_vseq #(
  .CFG_T               (usbdev_env_cfg),
  .RAL_T               (usbdev_reg_block),
  .COV_T               (usbdev_env_cov),
  .VIRTUAL_SEQUENCER_T (usbdev_virtual_sequencer)
);
`uvm_object_utils(usbdev_base_vseq)

usb20_item     m_usb20_item;
RSP            m_response_item;
token_pkt      m_token_pkt;
data_pkt       m_data_pkt;
handshake_pkt  m_handshake_pkt;
sof_pkt        m_sof_pkt;
// Selected device address
rand bit [6:0] dev_addr;
// Current SETUP buffer number
bit [4:0] setup_buffer_id = 5'd1;
// Current OUT buffer number
bit [4:0] out_buffer_id = 5'd7;
// Current IN buffer number
bit [4:0] in_buffer_id = 5'd13;

// Chosen /default/ endpoint, for those sequences concerned with only a single endpoint.
rand bit [3:0] ep_default;
constraint ep_default_c {
  ep_default inside {[0:NEndpoints-1]};
}

// Configured inter-packet delays; 0 = randomize across valid range.
int unsigned setup_data_delay = 0;
int unsigned out_data_delay   = 0;

// Bus events/stimuli to be presented during the sequence
//   (these are used in the `aon_wake_` and `rand_bus...` tests points).
bit do_reset_signaling  = 1'b0;
bit do_resume_signaling = 1'b0;
bit do_vbus_disconnects = 1'b0;

// Connect the usb20_agent via the block level interface?
bit do_agent_connect = 1'b1;

// Activate the usb20 agent via the block level interface?
bit do_agent_activate = 1'b1;

// Connect the USBDEV to the USB by supplying some basic register configuration?
bit do_usbdev_init = 1'b1;

// add post_reset_delays for sync between bus clk and usb clk in the apply_reset task
bit apply_post_reset_delays_for_sync = 1'b1;

// PHY Configuration that will rarely be changed; only required for very specific sequences.
bit phy_eop_single_bit = 1'b0;  // Note: the default reset value is 1
bit phy_usb_ref_disable = 1'b0;
bit phy_tx_osc_test_mode = 1'b0;
// TODO: support pin-flipping through the DV including the usb20_driver and usb20_monitor.
bit phy_pinflip = 1'b0;

// Approx. over-estimate of the USBDEV:AON/Wake clock ratio; we expect the USB device to be
// operating at no more than 48.24kHz, and the AON/Wake module to be operating at >= 200KHz.
// In fact we have permitted a ratio of up to 300:1 in the constraints.
uint usbdev_aon_wake_clk_ratio = 300;
// but we also have the two-cycle CDC synchronizer to consider.
uint aon_wake_control_wr_clks = (1 + 2) * usbdev_aon_wake_clk_ratio;
uint aon_wake_events_rd_clks = usbdev_aon_wake_clk_ratio;

// Controls exclusive access to the USB 2.0 driver.
// - some multi-stage operations must be performed atomically,
//   eg. token packet and handshake response, or VBUS connection and Bus Reset.
semaphore m_drv_lock;

`uvm_object_new

// Override apply_reset to cater to AON domain and host as well.
virtual task apply_reset(string kind = "HARD");
  fork
    if (kind == "HARD") begin
      // Ensure that the AON domain (slower clock) is in reset when the DUT domain
      // leaves reset, to prevent X propagation into the DUT.
      cfg.aon_clk_rst_vif.drive_rst_pin(0);
      // Explicitly specify a shorter reset interval to prevent test timeout.
      cfg.aon_clk_rst_vif.apply_reset(.reset_width_clks($urandom_range(5, 10)));
    end
    if (kind == "HARD" || kind == "BUS_IF") begin
      super.apply_reset("HARD");
    end
    if (kind == "HARD") begin
      cfg.host_clk_rst_vif.apply_reset();
    end
  join
  do_apply_post_reset_delays_for_sync();
endtask

virtual task apply_resets_concurrently(int reset_duration_ps = 0);
  // Assert other resets.
  cfg.aon_clk_rst_vif.drive_rst_pin(0);
  cfg.host_clk_rst_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.aon_clk_rst_vif.clk_period_ps);
  // Release resets.
  cfg.aon_clk_rst_vif.drive_rst_pin(1);
  cfg.host_clk_rst_vif.drive_rst_pin(1);
endtask

// Apply additional delays at the dut_init stage when either apply_reset or
// wait_for_reset is called. The additional delays allow the logic to sync
// across clock domains so that the Dut behaves deterministically. To disable
// this, set apply_post_reset_delays_for_sync in the extended class' pre_start.
virtual task do_apply_post_reset_delays_for_sync();
  if (apply_post_reset_delays_for_sync) begin
    fork
      cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
      cfg.aon_clk_rst_vif.wait_clks($urandom_range(5, 10));
      cfg.host_clk_rst_vif.wait_clks($urandom_range(5, 10));
    join
  end
endtask

// Override wait_for_reset to cater to AON domain as well.
virtual task wait_for_reset(string reset_kind     = "HARD",
  bit wait_for_assert   = 1,
  bit wait_for_deassert = 1);

  fork
    // main DUT reset.
    if (reset_kind == "HARD" || reset_kind == "BUS_IF") begin
      super.wait_for_reset(reset_kind, wait_for_assert, wait_for_deassert);
    end
    // reset for usbdev_aon_wake module.
    if (reset_kind == "HARD") begin
      if (wait_for_assert) begin
        `uvm_info(`gfn, "waiting for aon_rst_n assertion...", UVM_MEDIUM)
        @(negedge cfg.aon_clk_rst_vif.rst_n);
      end
      if (wait_for_deassert) begin
        `uvm_info(`gfn, "waiting for aon_rst_n de-assertion...", UVM_MEDIUM)
        @(posedge cfg.aon_clk_rst_vif.rst_n);
      end
    end
    // reset for host model.
    if (reset_kind == "HARD") begin
      if (wait_for_assert) begin
        `uvm_info(`gfn, "waiting for host_rst_n assertion...", UVM_MEDIUM)
        @(negedge cfg.host_clk_rst_vif.rst_n);
      end
      if (wait_for_deassert) begin
        `uvm_info(`gfn, "waiting for host_rst_n de-assertion...", UVM_MEDIUM)
        @(posedge cfg.host_clk_rst_vif.rst_n);
      end
    end
  join
  `uvm_info(`gfn, "usbdev wait_for_reset done", UVM_HIGH)
  do_apply_post_reset_delays_for_sync();
endtask

  // Give derived sequences the opportunity to override the connection of the usb20_agent via the
  // the interface.
  virtual task pre_start();
    // These options constrain the inter-packet delays for DATA packets following SETUP and OUT
    // token packets; default to zero (above) for randomized delays across the valid range.
    // The values are specified in 48MHz clock ticks (1/4 bit intervals) because we need 0.5 bit
    // interval granularity.
    void'($value$plusargs("setup_data_delay=%0d", setup_data_delay));
    void'($value$plusargs("out_data_delay=%0d", out_data_delay));
    // These options are common to a few tests, but will not be specified for most so they default
    // to zero (above).
    void'($value$plusargs("do_reset_signaling=%0b",  do_reset_signaling));
    void'($value$plusargs("do_resume_signaling=%0b", do_resume_signaling));
    void'($value$plusargs("do_vbus_disconnects=%0b", do_vbus_disconnects));

    // Create the lock controlling exclusive access to the driver.
    m_drv_lock = new(1);

    if (do_agent_connect) begin
      // Connect the USB20 agent and ensure that the USBDPI model is not connected.
      cfg.m_usb20_agent_cfg.bif.enable_driver(1'b1);
      cfg.usb20_usbdpi_vif.enable_driver(1'b0);
      // Activate it as well? For common sequences we need defined inputs into the DUT to prevent
      // assertions and link-related interrupts from interfering with CSR tests, but we do not
      // want the usb20_agent to be active.
      if (do_agent_activate) begin
        cfg.m_usb20_agent_cfg.bif.activate_driver(1'b1);
      end
    end
    super.pre_start();
  endtask

  // Override dut_init to do some basic usbdev initializations (if enabled).
  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_usbdev_init) begin
      // Default bus configuration; these will potentially impact all test sequences, so it's
      // preferable to modify the test configurations rather than change these defaults.
      bit tx_use_d_se0 = 0;
      bit en_diff_rcvr = 1;
      bit pin_flip = 0;
      void'($value$plusargs("pin_flip=%d", pin_flip)); // Flip pins on the USB?
      void'($value$plusargs("en_diff_rcvr=%d", en_diff_rcvr)); // Enable differential receiver?
      void'($value$plusargs("tx_use_d_se0=%d", tx_use_d_se0)); // Use D/SE0 for transmission?
      // Initialize the device via its registers.
      usbdev_init(dev_addr, en_diff_rcvr, tx_use_d_se0, pin_flip);
    end
  endtask

  // Wait for the DUT to enter one of the given link states, with an optional timeout
  //   (the default of -1 disables the timeout).
  // Link state transitions occur in response to bus activity from the host driving the USB.
  virtual task wait_for_link_state(usbdev_link_state_e states[], int timeout_clks = -1,
                                   bit fatal = 1);
    // Wait until the given state is attained or the (optionally
    usbdev_link_state_e rd;
    do begin
      uvm_reg_data_t data;
      // Delay and if timeout was requested, decrease the cycle count.
      cfg.clk_rst_vif.wait_clks(128);
      if (timeout_clks >= 0) timeout_clks -= (timeout_clks > 128) ? 128 : timeout_clks;
      csr_rd(.ptr(ral.usbstat.link_state), .value(data));
      rd = usbdev_link_state_e'(data);
    end while (!(rd inside {states}) && (timeout_clks != 0));
    if (fatal && !(rd inside {states})) begin
      `dv_fatal($sformatf("DUT did not enter expected link state (still in %d)", rd))
    end
  endtask

  // Claim exclusive access to the USB 2.0 driver.
  virtual task claim_driver();
    m_drv_lock.get(1);
  endtask

  // Release access to the USB 2.0 driver.
  virtual task release_driver();
    m_drv_lock.put(1);
  endtask

  // Construct and transmit a token packet to the USB device
  virtual task send_token_packet(bit [3:0] ep, pid_type_e pid_type, bit inject_crc_error = 0);
    `uvm_create_on(m_token_pkt, p_sequencer.usb20_sequencer_h)
    start_item(m_token_pkt);
    m_token_pkt.m_ev_type  = EvPacket;
    m_token_pkt.m_pkt_type = PktTypeToken;
    m_token_pkt.m_pid_type = pid_type;
    assert(m_token_pkt.randomize() with {m_token_pkt.address == dev_addr;
                                         m_token_pkt.endpoint == ep;});
    // Any fault injections requested?
    if (inject_crc_error) m_token_pkt.crc5 = ~m_token_pkt.crc5;
    m_usb20_item = m_token_pkt;
    finish_item(m_token_pkt);
  endtask

  // Send a DATA packet to the USB device, retaining a copy for subsequent checks.
  virtual task send_data_packet(input pid_type_e pid_type, input byte unsigned data[],
                                input bit isochronous_transfer = 1'b0);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    start_item(m_data_pkt);
    m_data_pkt.m_ev_type  = EvPacket;
    m_data_pkt.m_pkt_type = PktTypeData;
    m_data_pkt.m_pid_type = pid_type;
    if (isochronous_transfer) begin
      m_data_pkt.m_usb_transfer = usb_transfer_e'(IsoTrans);
    end
    m_data_pkt.set_data(data);  // This also completes the CRC16.
    m_usb20_item = m_data_pkt;
    finish_item(m_data_pkt);
  endtask

  // Construct and transmit a randomized DATA packet to the USB device, retaining a copy for
  // subsequent checks.
  virtual task send_prnd_data_packet(input pid_type_e pid_type,
                             input bit randomize_length, input bit [6:0] num_of_bytes,
                             input bit isochronous_transfer = 1'b0);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    start_item(m_data_pkt);
    m_data_pkt.m_ev_type  = EvPacket;
    m_data_pkt.m_pkt_type = PktTypeData;
    m_data_pkt.m_pid_type = pid_type;
    if (isochronous_transfer) begin
      m_data_pkt.m_usb_transfer = usb_transfer_e'(IsoTrans);
    end
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_data_pkt,
                                   !randomize_length -> m_data_pkt.data.size() == num_of_bytes;)
    m_usb20_item = m_data_pkt;
    finish_item(m_data_pkt);
  endtask

  // Construct and transmit a randomized OUT DATA packet, retaining a copy for subsequent checks.
  virtual task send_prnd_setup_packet(bit [3:0] ep);
    // Send SETUP token packet to the selected endpoint on the specified device.
    send_token_packet(ep, PidTypeSetupToken);
    // Variable delay between SETUP token packet and the ensuing DATA packet.
    inter_packet_delay(setup_data_delay);
    // DATA0/DATA packet with randomized content, but we'll honor the rule that SETUP DATA packets
    // are 8 bytes in length. The DUT does not attempt to interpret the packet content.
    send_prnd_data_packet(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(8));
  endtask

  // Construct and transmit a randomized OUT DATA packet, retaining a copy for subsequent checks.
  virtual task send_prnd_out_packet(bit [3:0] ep, input pid_type_e pid_type,
                                    input bit randomize_length, input bit [6:0] num_of_bytes,
                                    bit isochronous_transfer = 1'b0);
    // Send OUT token packet to the selected endpoint on the specified device.
    send_token_packet(ep, PidTypeOutToken);
    // Variable delay between OUT token packet and the ensuing DATA packet.
    inter_packet_delay(out_data_delay);
    // DATA0/DATA packet with randomized content.
    send_prnd_data_packet(pid_type, randomize_length, num_of_bytes, isochronous_transfer);
  endtask

  // Construct and transmit an OUT DATA packet containing the supplied data.
  virtual task send_out_packet(bit [3:0] ep, input pid_type_e pid_type, byte unsigned data[],
                               bit isochronous_transfer = 1'b0, bit [6:0] dev_address = dev_addr);
    // Send OUT token packet to the selected endpoint on the specified device.
    send_token_packet(ep, PidTypeOutToken);
    // Variable delay between OUT token packet and the ensuing DATA packet.
    inter_packet_delay(out_data_delay);
    // DATA0/DATA1 packet with the given content.
    send_data_packet(pid_type, data, isochronous_transfer);
  endtask

  // Retrieve the DUT response and check the Packet IDentifier against expectations.
  virtual task check_response_matches(input pid_type_e pid_type);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    m_usb20_item.check_pid_type(pid_type);
  endtask

  // Retrieve the DUT response to an IN transaction, and check that it matches expectations.
  virtual task check_in_packet(input pid_type_e pid_type, input byte unsigned data[]);
    data_pkt in_data;
    check_response_matches(pid_type);
    $cast(in_data, m_response_item);
    check_tx_packet(in_data, pid_type, data);
  endtask

  // Send handshake to DUT after an appropriate turn-around delay.
  virtual task send_handshake(input pid_type_e pid_type);
    // Must delay for a few bit intervals before responding.
    response_delay();
    // Construct and send handshake response.
    `uvm_create_on(m_handshake_pkt, p_sequencer.usb20_sequencer_h)
    start_item(m_handshake_pkt);
    m_handshake_pkt.m_ev_type  = EvPacket;
    m_handshake_pkt.m_pkt_type = PktTypeHandshake;
    m_handshake_pkt.m_pid_type = pid_type;
    m_usb20_item = m_handshake_pkt;
    finish_item(m_handshake_pkt);
  endtask

  // Read and check the content of the given packet buffer against expectations.
  task read_check_buffer(bit [4:0] buffer_id, byte unsigned exp_data[]);
    int unsigned exp_size = exp_data.size();
    byte unsigned pkt_data[];
    bit mismatch = 0;

    // Collect the packet data from the buffer within the DUT.
    read_buffer(buffer_id, exp_size, pkt_data);
    `DV_CHECK_EQ_FATAL(pkt_data.size(), exp_size, "Unexpected packet size")

    // Check buffer content against packet data.
    for (int unsigned idx = 0; idx < exp_size; idx++) begin
      `uvm_info(`gfn, $sformatf("Checking %2d: 0x%02x against 0x%02x",
                                idx, pkt_data[idx], exp_data[idx]), UVM_HIGH)
      // `DV check on actual and exp data
      mismatch |= (pkt_data[idx] !== exp_data[idx]);
    end
    // Now that all data has been reported, stop if anything mismatched.
    `DV_CHECK_EQ(mismatch, 0, "Received buffer contents do not match expected data")
  endtask

  // Write some data into the USB device packet buffer memory.
  task write_buffer(bit [4:0] buffer_id, byte unsigned pkt_data[]);
    int unsigned pkt_size = pkt_data.size();
    int unsigned offset;
    `DV_CHECK(pkt_size <= MaxPktSizeByte);

    // Calculate start address (in 32-bit words) of buffer.
    offset = buffer_id * 'h10;

    `uvm_info(`gfn, $sformatf("write_buffer id %d with %d bytes", buffer_id, pkt_size), UVM_MEDIUM)
    for (int unsigned idx = 0; idx < pkt_size; idx++) begin
      `uvm_info(`gfn, $sformatf("%2d: 0x%02x", idx, pkt_data[idx]), UVM_HIGH)
    end

    // Note that unfortunately we can write only complete data words to the DUT; partial word
    // writes would raise an error if attempted using 'tl_access' because the packet buffer memory
    // itself does not offer lane enables.
    for (int unsigned idx = 0; idx < pkt_size; idx += 4) begin
      // Number of valid bytes within this word.
      int unsigned nb = (pkt_size - idx >= 4) ? 4 : (pkt_size - idx);
      bit [TL_DBW-1:0] mask = TL_DBW'((1 << nb) - 1);
      // Populate only the valid parts of the write data word, and importantly avoid
      // out-of-bounds accesses to 'pkt_data.'
      bit [TL_DW-1:0]  wdata;
      wdata[7:0] = pkt_data[idx];
      if (mask[1]) wdata[15:8]  = pkt_data[idx + 1];
      if (mask[2]) wdata[23:16] = pkt_data[idx + 2];
      if (mask[3]) wdata[31:24] = pkt_data[idx + 3];

      mem_wr(.ptr(ral.buffer), .offset(offset), .data(wdata));
      offset++;
    end
  endtask

  // Read and return data from the given packet buffer.
  task read_buffer(bit [4:0] buffer_id, int unsigned len, output byte unsigned data[]);
    // Calculate start address (in 32-bit words) of buffer
    int unsigned offset = buffer_id * 'h10;

    `DV_CHECK_FATAL(len <= MaxPktSizeByte);
    data = new [len];

    for (int unsigned idx = 0; idx < len; idx += 4) begin
      // Number of valid bytes within this word
      int unsigned nb = (len - idx >= 4) ? 4 : (len - idx);
      bit [TL_DBW-1:0] mask = TL_DBW'((1 << nb) - 1);
      bit [31:0] act_data;

      // We can only read complete bus words from the packet buffer memory, but the USB packet
      // lengths have byte-level granularity.
      mem_rd(.ptr(ral.buffer), .offset(offset), .data(act_data));
      data[idx] = act_data[7:0];
      if (mask[1]) data[idx + 1] = act_data[15:8];
      if (mask[2]) data[idx + 2] = act_data[23:16];
      if (mask[3]) data[idx + 3] = act_data[31:24];
      offset++;
    end
  endtask

  // Check that a SETUP/OUT data packet with the given properties was received and stored by
  // the USB device in its packet buffer memory.
  task check_rx_packet(bit [3:0] ep, bit setup, bit [4:0] buffer_id,
                       byte unsigned exp_byte_data[]);
    uvm_reg_data_t rx_fifo_read;

    // Read RX FIFO which should contain a buffer description matching the expectations
    csr_rd(.ptr(ral.rxfifo), .value(rx_fifo_read));

    `DV_CHECK_EQ(get_field_val(ral.rxfifo.ep, rx_fifo_read), ep);
    `DV_CHECK_EQ(get_field_val(ral.rxfifo.setup, rx_fifo_read), setup);
    `DV_CHECK_EQ(get_field_val(ral.rxfifo.buffer, rx_fifo_read), buffer_id);
    `DV_CHECK_EQ(get_field_val(ral.rxfifo.size, rx_fifo_read), exp_byte_data.size());

    read_check_buffer(buffer_id, exp_byte_data);
  endtask

  // Check that the IN DATA packet transmitted by the USB device matches our expectations
  task check_tx_packet(data_pkt pkt, pid_type_e exp_pid, input byte unsigned exp_data[]);
    int unsigned act_len = pkt.data.size();
    int unsigned exp_len = exp_data.size();
    int unsigned len = (act_len < exp_len) ? act_len : exp_len;

    `uvm_info(`gfn, $sformatf("IN packet PID 0x%x len %d expected PID 0x%x len %d",
                              pkt.m_pid_type, act_len, exp_pid, exp_len), UVM_HIGH)
    `DV_CHECK_EQ(pkt.m_pid_type, exp_pid);

    // Report all of the actual and expected bytes before checking, to aid diagnosis.
    for (int unsigned i = 0; i < exp_data.size(); i++) begin
      `uvm_info(`gfn, $sformatf("%d: 0x%x", i, exp_data[i]), UVM_HIGH)
    end
    for (int unsigned i = 0; i < pkt.data.size(); i++) begin
      `uvm_info(`gfn, $sformatf("%d: 0x%x", i, pkt.data[i]), UVM_HIGH)
    end
    for (int unsigned i = 0; i < len; i++) begin
      `DV_CHECK_EQ(pkt.data[i], exp_data[i], "Mismatch in packet data")
    end
    `DV_CHECK_EQ(act_len, exp_len, "Unexpected packet length")
  endtask

  task check_in_sent(bit [3:0] ep);
    bit pkt_sent;
    bit sent;
    csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
    csr_rd(.ptr(ral.in_sent[0].sent[ep]), .value(sent));
    `DV_CHECK_EQ(1, pkt_sent);
    `DV_CHECK_EQ(1, sent);

    // Write 1 to clear particular EP in_sent
    csr_wr(.ptr(ral.in_sent[0].sent[ep]), .value(1'b1));
    csr_rd(.ptr(ral.in_sent[0].sent[ep]), .value(sent));
    `DV_CHECK_EQ(sent, 0); // verify that after writing 1, the in_sent bit is cleared.
  endtask

  // Check that the USB device received a packet with the expected properties.
  task check_pkt_received(bit [3:0] ep, bit setup, bit [4:0] buffer_id,
                          byte unsigned exp_byte_data[]);
    uvm_reg_data_t intr_state;
    bit pkt_received;

    // Read intr_state reg
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // Get pkt_received interrupt status
    pkt_received = bit'(get_field_val(ral.intr_state.pkt_received, intr_state));
    // DV_CHECK on pkt_received interrupt; this is a Status type interrupt,
    // so it will be asserted only whilst the RX FIFO is non-empty.
    `DV_CHECK_EQ(pkt_received, 1);

    // Read rx_fifo reg, clearing the interrupt condition.
    check_rx_packet(ep, setup, buffer_id, exp_byte_data);

    // Read intr_state reg
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // Get pkt_received interrupt status
    pkt_received = bit'(get_field_val(ral.intr_state.pkt_received, intr_state));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(pkt_received, 0);
  endtask

  virtual task dut_shutdown();
    // check for pending usbdev operations and wait for them to complete
    // TODO
  endtask

  // Set up basic configuration, optionally using a specific device address
  virtual task usbdev_init(bit [TL_DW-1:0] device_address = 0,
                           // PHY Configuration for this test; all permutations should be tested.
                           bit use_diff_rcvr = 0, bit tx_use_d_se0 = 0, bit pinflip = 0);
    // Remember the pinflip setting.
    phy_pinflip = pinflip;
    // Configure PHY
    // - the different modes of operation may be set using parameters,
    ral.phy_config.use_diff_rcvr.set(use_diff_rcvr);
    ral.phy_config.tx_use_d_se0.set(tx_use_d_se0);
    ral.phy_config.pinflip.set(pinflip);
    // ... but these rarely require changing; only for very specific test sequences.
    ral.phy_config.eop_single_bit.set(phy_eop_single_bit);
    ral.phy_config.usb_ref_disable.set(phy_usb_ref_disable);
    ral.phy_config.tx_osc_test_mode.set(phy_tx_osc_test_mode);
    csr_update(ral.phy_config);
    // Has a specified address been requested? Zero is not a valid device address
    // on the USB except during the initial configuration process, so we'll just
    // keep the previous value if asked for zero.
    if (!device_address) begin
      device_address = dev_addr;
    end
    // Instruct the driver to assert VBUS to the DUT; this is akin to being plugged in.
    set_vbus_state(1);
    usbdev_connect();
    // Instruct the driver to perform Bus Reset Signaling; keep this to 100us since there's no
    // point wasting simulation time on all sequences. Full length resets are exercised in
    // usbdev_bus_rand_vseq.
    send_bus_reset(100);
    // Now that the Bus Reset has been completed we may set the device address without losing it.
    `uvm_info(`gfn, $sformatf("Setting device address to 0x%02x", device_address), UVM_MEDIUM)
    usbdev_set_address(device_address);
  endtask

  // Connect to the USB.
  virtual task usbdev_connect();
    ral.usbctrl.enable.set(1'b1);
    csr_update(ral.usbctrl);
  endtask

  // Disconnect from the USB.
  virtual task usbdev_disconnect();
    ral.usbctrl.enable.set(1'b0);
    csr_update(ral.usbctrl);
  endtask

  // Set the device address of the DUT on the USB.
  virtual task usbdev_set_address(bit [6:0] address);
    // Use this address for all subsequent token packets.
    dev_addr = address;
    // Inform the DUT of its assigned device address.
    ral.usbctrl.device_address.set(address);
    csr_update(ral.usbctrl);
  endtask

  // Configure all OUT endpoints for reception of OUT packets.
  virtual task configure_out_all();
    // Enable OUT endpoints
    csr_wr(.ptr(ral.ep_out_enable[0]), .value({NEndpoints{1'b1}}));
    // Enable rx out
    csr_wr(.ptr(ral.rxenable_out[0]), .value({NEndpoints{1'b1}}));
  endtask

  virtual task configure_out_trans(bit [3:0] ep);
    // Enable endpoint for OUT packet reception.
    csr_wr(.ptr(ral.ep_out_enable[0].enable[ep]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable rx out
    ral.rxenable_out[0].out[ep].set(1'b1);
    csr_update(ral.rxenable_out[0]);
    // Put buffer in Available OUT Buffer _FIFO_, so use csr_wr _not_ csr_update
    csr_wr(.ptr(ral.avoutbuffer.buffer), .value(out_buffer_id));
  endtask

  // Configure all OUT endpoints for reception of SETUP packets.
  virtual task configure_setup_all();
    // Enable OUT endpoints
    csr_wr(.ptr(ral.ep_out_enable[0]), .value({NEndpoints{1'b1}}));
    // Enable rx SETUP
    csr_wr(.ptr(ral.rxenable_setup[0]), .value({NEndpoints{1'b1}}));
    // Clear STALL by default, as a precaution.
    csr_wr(.ptr(ral.out_stall[0]), .value({NEndpoints{1'b1}}));
  endtask

  virtual task configure_setup_trans(bit [3:0] ep);
    // Enable EP0 Out
    csr_wr(.ptr(ral.ep_out_enable[0].enable[ep]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable rx setup
    ral.rxenable_setup[0].setup[ep].set(1'b1);
    csr_update(ral.rxenable_setup[0]);
    // Put buffer in Available SETUP Buffer _FIFO_, so use csr_wr _not_ csr_update
    csr_wr(.ptr(ral.avsetupbuffer.buffer), .value(setup_buffer_id));
  endtask

  // Configure all IN endpoints to respond to IN requests.
  virtual task configure_in_all();
    // Enable IN endpoints
    csr_wr(.ptr(ral.ep_in_enable[0]), .value({NEndpoints{1'b1}}));
  endtask

  // Configure an IN transaction on a specific endpoint.
  virtual task configure_in_trans(bit [3:0] ep, bit [4:0] buffer_id, bit [6:0] num_of_bytes);
    // Enable EP0 IN
    csr_wr(.ptr(ral.ep_in_enable[0].enable[ep]),  .value(1'b1));
    csr_update(ral.ep_in_enable[0]);
    // Configure IN Transaction
    ral.configin[ep].rdy.set(1'b1);
    ral.configin[ep].size.set(num_of_bytes);
    ral.configin[ep].buffer.set(buffer_id);
    csr_update(ral.configin[ep]);
  endtask

  // Send 'Start Of Frame' packet (bus frame/timing referenace).
  virtual task send_sof_packet(input pid_type_e pid_type);
    `uvm_create_on(m_sof_pkt, p_sequencer.usb20_sequencer_h)
    start_item(m_sof_pkt);
    m_sof_pkt.m_ev_type  = EvPacket;
    m_sof_pkt.m_pkt_type = PktTypeSoF;
    m_sof_pkt.m_pid_type = pid_type;
    assert(m_sof_pkt.randomize());
    m_usb20_item = m_sof_pkt;
    finish_item(m_sof_pkt);
  endtask

  // Perform Suspend Signaling (Idle state). 0 = Use default duration.
  virtual task send_suspend_signaling(int unsigned duration_usecs = 0);
    usb20_item item;
    // Suspend Signaling.
    `uvm_create_on(item, p_sequencer.usb20_sequencer_h)
    start_item(item);
    item.m_ev_type = EvSuspend;
    item.m_ev_duration_usecs = duration_usecs;
    finish_item(item);
    // Block until Suspend Signaling has been completed.
    get_response(m_response_item);
  endtask

  // Perform Resume Signaling on the USB; this instructs the DUT to exit a Suspended state.
  // 0 = Use default duration.
  virtual task send_resume_signaling(int unsigned duration_usecs = 0);
    usb20_item item;
    // Send Resume Signaling.
    `uvm_create_on(item, p_sequencer.usb20_sequencer_h)
    start_item(item);
    item.m_ev_type = EvResume;
    item.m_ev_duration_usecs = duration_usecs;
    finish_item(item);
    // Block until Resume Signaling has been completed.
    get_response(m_response_item);
  endtask

  // Issue a Bus Reset to the DUT. 0 = Use default duration.
  virtual task send_bus_reset(int unsigned duration_usecs = 0);
    usb20_item item;
    `uvm_create_on(item, p_sequencer.usb20_sequencer_h)
    start_item(item);
    item.m_ev_type = EvBusReset;
    item.m_ev_duration_usecs = duration_usecs;
    finish_item(item);
    // Block until Reset Signaling is complete.
    get_response(m_response_item);
  endtask

  // Set the state of the VBUS signal from the usb20_driver, indicating the presence/absence
  // of a host connection.
  virtual task set_vbus_state(bit enabled);
    usb20_item item;
    `uvm_create_on(item, p_sequencer.usb20_sequencer_h)
    start_item(item);
    item.m_ev_type = enabled ? EvConnect : EvDisconnect;
    finish_item(item);
    // Block until VBUS change has occurred.
    get_response(m_response_item);
  endtask

  // Hand over control of the USB to the AON/Wake module.
  virtual task aon_wake_activate();
    bit active = 1'b0;
    ral.wake_control.suspend_req.set(1'b1);
    csr_update(.csr(ral.wake_control));
    aon_wake_wait_status(1'b1, active);
    `DV_CHECK_EQ(active, 1'b1, "AON/Wake module did not become active when expected")
  endtask

  // Recover control of the USB from the AON/Wake module.
  virtual task aon_wake_deactivate();
    bit active = 1'b1;
    ral.wake_control.wake_ack.set(1'b1);
    csr_update(.csr(ral.wake_control));
    aon_wake_wait_status(1'b0, active);
    `DV_CHECK_EQ(active, 1'b0, "AON/Wake module did not deactivate as expected")
  endtask

  // Wait until the 'module_active' status indicator has the desired value or it has not
  // changed within the expected interval.
  virtual task aon_wake_wait_status(bit exp_active, output bit active);
    // The 'control' write into the AON/Wake domain takes some time because of its much slower
    // clock frequency, and then we must read back the status indication too.
    uint delay_max = aon_wake_control_wr_clks + aon_wake_events_rd_clks;
    for (int unsigned i = 0; i < delay_max; i++) begin
      // Wait until the AON/Wake module indicates that it is inactive.
      csr_rd(.ptr(ral.wake_events.module_active), .value(active));
      if (active == exp_active) break;
    end
  endtask

  // It takes a little whilst for the register state to propagate out and back in through the
  // synchronizers, eg. pull up assertion or software direct drive.
  virtual task loopback_delay();
    cfg.clk_rst_vif.wait_clks(5);
  endtask

  virtual task inter_packet_delay(int delay = 0);
    // From section 7.1.18.1 Time interval between packets is between 2 and 6.5 bit times.
    if (delay == 0) delay = $urandom_range(8, 26);
    else begin
      // Delay in host-side clock cycles may be specified explicitly to achieve min or max value.
      `DV_CHECK(delay >= 8 && delay <= 26);
    end
    cfg.host_clk_rst_vif.wait_clks(delay);
  endtask

  virtual task response_delay(int delay = 0);
    // From section 7.1.18.1 Time interval between packets is between 2 and 7.5 bit times.
    if (delay == 0) delay = $urandom_range(8, 30);
    else begin
      // Delay in host-side clock cycles may be specified explicitly to achieve min or max value.
      `DV_CHECK(delay >= 8 && delay <= 30);
    end
    cfg.host_clk_rst_vif.wait_clks(delay);
  endtask
endclass : usbdev_base_vseq
