// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A reactive sequence that responds to requests, responding with a digest each time.

class kmac_app_device_seq extends dv_base_seq #(.REQ (kmac_app_rsp_item),
                                                .CFG_T (kmac_app_agent_cfg),
                                                .SEQUENCER_T (kmac_app_device_sequencer));
  `uvm_object_utils(kmac_app_device_seq)

  extern function new (string name="");
  extern virtual task body();

  extern local task send_response(kmac_app_req_packet_item req);
endclass

function kmac_app_device_seq::new(string name="");
  super.new(name);
endfunction

task kmac_app_device_seq::body();
  forever begin
    kmac_app_req_packet_item req;
    p_sequencer.m_req_fifo.get(req);
    send_response(req);
  end
endtask

task kmac_app_device_seq::send_response(kmac_app_req_packet_item req);
  kmac_app_rsp_item item = kmac_app_rsp_item::type_id::create("item");
  kmac_pkg::rsp_digest_t rsp_digest_h = '0;
  bit gen_error, set_digest;

  if (cfg.has_user_digest()) begin
    set_digest = 1;
    rsp_digest_h = cfg.pop_user_digest();
  end else begin
    set_digest = 0;
  end

  start_item(item);

  gen_error = $urandom_range(100, 1) <= cfg.error_rsp_pct;

  if (!item.randomize() with {
        if (local::set_digest) {
          m_digest_share0 == local::rsp_digest_h.digest_share0;
          m_digest_share1 == local::rsp_digest_h.digest_share1;
        }

        local::gen_error == (m_error ||
                             (cfg.constant_share_means_error &&
                              (&m_digest_share0 || ~|m_digest_share0 ||
                               &m_digest_share1 || ~|m_digest_share1)));

        if (cfg.zero_delays) {
          m_delay == 0;
        } else {
          cfg.rsp_delay_min <= m_delay;
          m_delay <= cfg.rsp_delay_max;
        }
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomize response.")
  end

  finish_item(item);
endtask
