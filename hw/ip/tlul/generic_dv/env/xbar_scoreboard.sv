// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ------------------------------------------------------------------------
// Xbar scoreboard class
// Extend from common multi-streams scoreboard
// Use the device address map to determine the queue ID
// ------------------------------------------------------------------------
class xbar_scoreboard extends scoreboard_pkg::scoreboard #(.ITEM_T(tl_seq_item),
                                                           .CFG_T (xbar_env_cfg),
                                                           .COV_T (xbar_env_cov));
  int chan_prefix_len = 7;

  `uvm_component_utils(xbar_scoreboard)
  `uvm_component_new

  // Customize the get_queue_name function
  // port_name is {"a/d_chan_", host/devce name}
  // tl_channel is "a/d_chan_"
  // tl_port is host/devce name
  virtual function string get_queue_name(tl_seq_item tr, string port_name);
    string queue_name;
    string tl_channel;
    string tl_port;
    tl_channel = port_name.substr(0, chan_prefix_len-1);

    tl_port = port_name.substr(chan_prefix_len, port_name.len() - 1);
    if (!port_dir.exists(port_name)) begin
      `uvm_fatal(`gfn, $sformatf("Unexpected port name %0s", tl_port))
    end begin
      queue_name = get_queue_full_name(tr, tl_port, tl_channel);
    end
    `uvm_info(`gfn, $sformatf("Scoreboard queue name : %0s", queue_name), UVM_HIGH)
    return queue_name;
  endfunction

  // queue name is a_chan_``device_name`` or d_chan_``device_name``, device name is its suffix
  // a_chan_/d_chan_ is prefix, which is from input queue_prefix
  // if port is a device, return {queue_prefix, device_name}
  // if port is a host, need to find the pair device_name, then return {queue_prefix, device_name}
  // if unmapped addr, src is host a_chan, dst is host d_chan, so,
  // use another prefix and return {"host_unmapped_addr_", host_name}
  virtual function string get_queue_full_name(tl_seq_item tr,
                                              string      tl_port,
                                              string      queue_prefix);
    foreach (xbar_devices[i]) begin
      if (xbar_devices[i].device_name == tl_port) return {queue_prefix, tl_port};
    end
    foreach (xbar_hosts[i]) begin
      if (xbar_hosts[i].host_name == tl_port) begin
        // Current port is a host port, get pair device port from the address
        foreach (xbar_devices[j]) begin
          if (xbar_devices[j].device_name inside {xbar_hosts[i].valid_devices} &&
              is_device_valid_addr(xbar_devices[j].device_name, tr.a_addr)) begin
              return {queue_prefix, xbar_devices[j].device_name};
          end
        end
        // it's unmapped address
        `uvm_info(`gfn, $sformatf("Unmapped addr: 0x%0h at %0s", tr.a_addr, tl_port), UVM_HIGH)
        return {"host_unmapped_addr_", tl_port};
      end
    end
    `uvm_error(`gfn, $sformatf("Found unexpected item at[%0s]: %0s",
                                tl_port, tr.convert2string()))
  endfunction

  // from host to device, source ID may be changed and set all source ID to 0
  function tl_seq_item modify_source_id(tl_seq_item tr);
    tl_seq_item tr_modified;
    `downcast(tr_modified, tr.clone());
    tr_modified.a_source = 0;
    tr_modified.d_source = 0;
    return tr_modified;
  endfunction

  // check if the item is from host and it has mapped address
  function bit is_access_to_mapped_addr(tl_seq_item tr, string port_name);
    string tl_port;
    tl_port = port_name.substr(chan_prefix_len, port_name.len() - 1);
    foreach (xbar_hosts[i]) begin
      if (xbar_hosts[i].host_name == tl_port) begin
        foreach (xbar_devices[j]) begin
          if (xbar_devices[j].device_name inside {xbar_hosts[i].valid_devices} &&
              is_device_valid_addr(xbar_devices[j].device_name, tr.a_addr)) begin
            if (cfg.en_cov) cov.host_access_mapped_addr_cg[tl_port].sample(1);
            return 1; // host port and mapped address
          end
        end
        if (cfg.en_cov) cov.host_access_mapped_addr_cg[tl_port].sample(0);
        return 0; // host port, but unmapped address
      end
    end
    return 1; // not host port
  endfunction

  virtual function void process_src_packet(input tl_seq_item  tr,
                                           input string port_name,
                                           output tl_seq_item transformed_tr[$]);
    tl_seq_item modified_tr;
    if (is_access_to_mapped_addr(tr, port_name)) begin
      modified_tr = modify_source_id(tr);
      // d_data is 0, when it's a write
      if (modified_tr.d_opcode == tlul_pkg::AccessAck) modified_tr.d_data = 0;
      transformed_tr = {modified_tr};
    end else begin
      tl_seq_item rsp;
      `downcast(rsp, tr.clone());
      rsp.d_source    = tr.a_source;
      rsp.d_size      = tr.a_size;
      rsp.d_error     = 1;
      rsp.d_data      = rsp.a_opcode == tlul_pkg::Get ? '1 : 0;
      rsp.d_opcode    = rsp.a_opcode == tlul_pkg::Get ?
                        tlul_pkg::AccessAckData : tlul_pkg::AccessAck;
      transformed_tr  = {rsp};
    end
  endfunction

  virtual function void process_dst_packet(input tl_seq_item tr,
                                           input string port_name,
                                           output tl_seq_item transformed_tr);
    // if item is mapped, item will pass from h2d or d2h, source id may be changed and we don't
    // predict it, modify all source_id to 0.
    // if unmapped, item isn't passed down. source id shouldn't be changed. Check it
    if (is_access_to_mapped_addr(tr, port_name)) transformed_tr = modify_source_id(tr);
    else                                         transformed_tr = tr;
  endfunction

  function string get_tl_port(string port_name);
    return port_name.substr(chan_prefix_len, port_name.len()-1);
  endfunction

endclass
