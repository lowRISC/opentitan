// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_tx_rx_disruption_vseq extends usbdev_smoke_vseq;
  `uvm_object_utils(usbdev_tx_rx_disruption_vseq)

  `uvm_object_new

  // The type of disruption stimulus to generate.
  typedef enum {
    StimType_IPReset,
    StimType_BusReset,
    StimType_Disconnect
  } stim_type_e;

  // The type of transaction to interrupt.
  typedef enum {
    TxnType_SETUP,
    TxnType_OUT,
    TxnType_IN
  } txn_type_e;

  rand txn_type_e txn_type;   // The type of transaction to disrupt.
  rand bit disrupt_data;      // Disrupt the DATA packet rather than the token packet?
  rand stim_type_e stim_type; // Type of stimulus to be applied.

  // We run this sequence in normal differential mode (DP/DN for both IN and OUT) as well as
  // using 'd_se0' for transmission to help with coverage numbers.
  virtual task pre_start();
    phy_tx_use_d_se0 = $urandom & 1;
    super.pre_start();
  endtask

  virtual task body;
    // It can take 3-4 microseconds for the DUT to spot a link reset condition and we wish to be
    // able to induce one whilst it is still within what it thinks is the data field of a DATA
    // packet, so that must take at least 4 microseconds to transmit; this is 4 x 12 = 48 bit
    // intervals, or 6 bytes; making them appreciably longer just makes it less likely that we hit
    // the CRC bytes.
    byte unsigned data[$];
    // For attaining coverage numbers, however, we also want to ensure the 'out_state_q' FSM in
    // `usb_fs_tx` is observed moving through each of its 4 transitions, and there's only a 1/32
    // probability of a `link_reset` starting in the single cycle of fetch a new byte from the
    // packet buffer RAM, so use some longer packets too.
    uint data_bytes = ($urandom & 1) ? MaxPktSizeByte : 8;
    // Report choices.
    string stim_desc;
    // TODO: Only BusReset is expected to work presently; scoreboard/BFM not hooked up for IP reset.
    stim_type = StimType_BusReset;
    case (stim_type)
      StimType_IPReset:    stim_desc = "IP Reset";
      StimType_BusReset:   stim_desc = "Bus Reset";
      StimType_Disconnect: stim_desc = "Disconnect";
      default:             `uvm_fatal(`gfn, $sformatf("Invalid/unsupported stimulus %p", stim_type))
    endcase
    `uvm_info(`gfn, $sformatf("Disrupting %p data %0d with %s", txn_type, disrupt_data, stim_desc),
              UVM_LOW)
    // Use zeros for transferred data to avoid bit stuffing; we then guarantee that the tx/rx
    // _can_ be disrupted in the CRC at the packet end.
    repeat (data_bytes) data.push_back(0);

    // Set up the device and run the smoke sequence.
    super.body();

    // Initiate the transaction that we are going to disrupt.
    //
    // Keep the packets short; greater likelihood of disruption within the packet overhead (SYNC,
    // PID, CRC...), and it's also compatible with standard SETUP DATA packets.
    case (txn_type)
      TxnType_SETUP, TxnType_OUT: begin
        disrupt_tx_bits = disrupt_data ? 0 : $urandom_range(1, 31);  // Token packets are 32 bits.
        if (txn_type == TxnType_SETUP) send_token_packet(ep_default, PidTypeSetupToken);
        else send_token_packet(ep_default, PidTypeOutToken);
        if (disrupt_data) begin
          // Variable delay between OUT token packet and the ensuing DATA packet.
          inter_packet_delay();
          // Minimum length, with no bit stuffing, minus 1 becomes the upper bound.
          disrupt_tx_bits = $urandom_range(1, 31 + data_bytes * 8);
          // The selected PID type does not matter, for once; we're about to interrupt the
          // transmission.
          send_data_packet(PidTypeData0, data);
        end
      end
      TxnType_IN: begin
        configure_in_trans(ep_default, in_buffer_id, data_bytes);
        write_buffer(in_buffer_id, data);
        disrupt_tx_bits = disrupt_data ? 0 : $urandom_range(1, 31);  // Token packets are 32 bits.
        // Minimum length, with no bit stuffing, minus 1 becomes the upper bound.
        disrupt_rx_bits = disrupt_data ? $urandom_range(1, 31 + data_bytes * 8) : 0;
        send_token_packet(ep_default, PidTypeInToken);
        if (disrupt_data) begin
          RSP rsp;
          get_response(rsp);
        end
      end
      default: `uvm_fatal(`gfn, "Invalid/unrecognised transaction type")
    endcase
    // Switch off disruption before causing any further confusion.
    disrupt_tx_bits = 0;
    disrupt_rx_bits = 0;
    // Apply the disruption stimulus immediately.
    `uvm_info(`gfn, $sformatf("Applying %s stimulus to disrupt traffic", stim_desc), UVM_LOW)
    case (stim_type)
      StimType_BusReset: begin
        send_bus_reset(100);
        // After the Bus Reset we must reinstate the device address.
        `uvm_info(`gfn, $sformatf("Setting device address to 0x%02x", dev_addr), UVM_MEDIUM)
        usbdev_set_address(dev_addr);
      end
      StimType_IPReset: begin
        apply_reset();
        // After an IP block reset the entire device configuration must be reinstated.
        usbdev_init(dev_addr, phy_use_diff_rcvr, phy_tx_use_d_se0, phy_pinflip);
      end
      StimType_Disconnect: begin
        bit remove_pullup = $urandom & 1;
        set_vbus_state(0);
        // Wait for 100 microseconds; a pretty arbitrary choice. VBUS disconnections would usually
        // be longer in practice.
        cfg.clk_rst_vif.wait_clks(100 * 48);
        if (remove_pullup) begin
          usbdev_disconnect();
          set_vbus_state(1);
          // Wait a little before reinstating pull up
          cfg.clk_rst_vif.wait_clks(4 * 48);
          usbdev_connect();
        end else set_vbus_state(1);
        // Allow a little time before VBUS connection and the host supplying the Bus Reset.
        cfg.clk_rst_vif.wait_clks(10 * 48);
        send_bus_reset(100);
        // After the Bus Reset we must reinstate the device address.
        `uvm_info(`gfn, $sformatf("Setting device address to 0x%02x", dev_addr), UVM_MEDIUM)
        usbdev_set_address(dev_addr);
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected stimulus %p", stim_type))
    endcase

    // Try the smoke sequence again.
    super.body();
    // Choose another endpoint.
    ep_default = (|ep_default ? ep_default : NEndpoints) - 1;
    // Retry the smoke sequence.
    super.body();
  endtask

endclass : usbdev_tx_rx_disruption_vseq
