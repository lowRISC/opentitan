// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ------------------------------------------------------------------------
// Xbar scoreboard class
// Extend from common multi-streams scoreboard
// Use the device address map to determine the queue ID
// ------------------------------------------------------------------------
class xbar_scoreboard extends scoreboard_pkg::scoreboard#(tl_seq_item);

  xbar_env_cfg cfg;
  xbar_env_cov cov;
  int          chan_prefix_len = 7;

  `uvm_component_utils(xbar_scoreboard)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Customize the get_queue_name function
  virtual function string get_queue_name(tl_seq_item tr, string port_name);
    string queue_name;
    string tl_channel;
    string tl_port;
    tl_channel = port_name.substr(0, chan_prefix_len-1);

    tl_port = port_name.substr(chan_prefix_len, port_name.len()-1);
    if (!port_dir.exists(port_name)) begin
      `uvm_fatal(get_full_name(), $sformatf("Unexpected port name %0s", tl_port))
    end begin
      queue_name = {tl_channel, get_queue_suffix_name(tr, tl_port)};
    end
    `uvm_info(get_full_name(), $sformatf("Scoreboard queue name : %0s", queue_name), UVM_HIGH)
    return queue_name;
  endfunction

  // queue name is a_chan_``device_name`` or d_chan_``device_name``, device name is its suffix
  // if port is a device, return device name
  // if port is a host, need to find the pair device_name
  virtual function string get_queue_suffix_name(tl_seq_item tr, string port_name);
    foreach (xbar_devices[i]) begin
      if (xbar_devices[i].device_name == port_name) return port_name;
    end
    foreach (xbar_hosts[i]) begin
      if (xbar_hosts[i].host_name == port_name) begin
        // Current port is a host port, get pair device port from the address
        foreach (xbar_devices[j]) begin
          if (tr.a_addr inside {[xbar_devices[j].start_address : xbar_devices[j].end_address]})
            return xbar_devices[j].device_name;
        end
      end
    end
    // TODO(taliu) Determine how to handle unclaimed access
    `uvm_error(get_full_name(), $sformatf("Found unclaimed access[%0s]: %0s",
                                port_name, tr.convert2string()))
  endfunction

  // from host to device, source ID may be changed and set all source ID to 0
  function tl_seq_item modify_source_id(tl_seq_item tr);
    tl_seq_item tr_modified;
    `downcast(tr_modified, tr.clone());
    tr_modified.a_source = 0;
    tr_modified.d_source = 0;
    return tr_modified;
  endfunction

  virtual function void process_src_packet(input tl_seq_item  tr,
                                           input string port_name,
                                           output tl_seq_item transformed_tr[$]);
    transformed_tr = {modify_source_id(tr)};
  endfunction

  virtual function void process_dst_packet(input tl_seq_item tr,
                                           input string port_name,
                                           output tl_seq_item transformed_tr);
    transformed_tr = modify_source_id(tr);
  endfunction

  function string get_tl_port(string port_name);
    return port_name.substr(chan_prefix_len, port_name.len()-1);
  endfunction

endclass
