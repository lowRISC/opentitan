// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ------------------------------------------------------------------------
// Xbar scoreboard class
// Extend from common multi-streams scoreboard
// Use the device address map to determine the queue ID
// ------------------------------------------------------------------------
class xbar_scoreboard extends scoreboard_pkg::scoreboard#(tl_seq_item);

  int chan_prefix_len = 7;

  `uvm_component_utils(xbar_scoreboard)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Customize the get_queue_name function
  virtual function string get_queue_name(tl_seq_item tr, string port_name);
    string queue_name;
    string tl_channel;
    string tl_port;
    string pair_port_name;
    tl_channel = port_name.substr(0, chan_prefix_len-1);
    tl_port = port_name.substr(chan_prefix_len, port_name.len()-1);
    pair_port_name = get_pair_port_name(tr, tl_port);
    if (!port_dir.exists(port_name)) begin
      `uvm_fatal(get_full_name(), $sformatf("Unexpected port name %0s", tl_port))
    end else if (port_dir[port_name] == scoreboard_pkg::kSrcPort) begin
      queue_name = {tl_channel, tl_port, "_", pair_port_name};
    end else begin
      queue_name = {tl_channel, pair_port_name, "_", tl_port};
    end
    `uvm_info(get_full_name(), $sformatf("Scoreboard queue name : %0s", queue_name), UVM_HIGH)
    return queue_name;
  endfunction

  virtual function string get_pair_port_name(tl_seq_item tr, string port_name);
    foreach (xbar_hosts[i]) begin
      if (xbar_hosts[i].host_name == port_name) begin
        // Current port is a host port, get pair device port from the address
        foreach (xbar_devices[j]) begin
          if (tr.a_addr inside {[xbar_devices[j].start_address : xbar_devices[j].end_address]})
            return xbar_devices[j].device_name;
        end
      end
    end
    foreach (xbar_devices[i]) begin
      if (xbar_devices[i].device_name == port_name) begin
        // Current port is a device port, get pair host port from the source ID msb
        int host_id = tr.a_source[Valid_host_id_lsb-1:0];
        if (host_id >= xbar_hosts.size()) begin
          `uvm_error(get_full_name(), $sformatf("Out of range host id : %0d", host_id))
        end else begin
          return xbar_hosts[host_id].host_name;
        end
      end
    end
    // TODO(taliu) Determine how to handle unclaimed access
    `uvm_error(get_full_name(), $sformatf("Found unclaimed access[%0s]: %0s",
                                port_name, tr.convert2string()))
  endfunction

  // Adding host_id to the source ID to match the device side source ID
  virtual function void process_src_packet(input tl_seq_item  tr,
                                           input string port_name,
                                           output tl_seq_item transformed_tr[$]);
    int host_id = get_host_id(get_tl_port(port_name));
    if (host_id >= 0) begin
      tl_seq_item tr_modified;
      $cast(tr_modified, tr.clone());
      tr_modified.a_source = (tr_modified.a_source << Valid_host_id_lsb) | host_id;
      transformed_tr = {tr_modified};
    end else begin
      transformed_tr = {tr};
    end
  endfunction

  virtual function void process_dst_packet(input tl_seq_item tr,
                                           input string port_name,
                                           output tl_seq_item transformed_tr);
    int host_id = get_host_id(get_tl_port(port_name));
    if (host_id >= 0) begin
      $cast(transformed_tr, tr.clone());
      transformed_tr.a_source = (transformed_tr.a_source << Valid_host_id_lsb) | host_id;
      transformed_tr.d_source = (transformed_tr.d_source << Valid_host_id_lsb) | host_id;
    end else begin
      transformed_tr = tr;
    end
  endfunction

  function string get_tl_port(string port_name);
    return port_name.substr(chan_prefix_len, port_name.len()-1);
  endfunction

endclass
