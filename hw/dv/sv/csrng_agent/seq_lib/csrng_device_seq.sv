// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Response sequence for csrng protocols.
// This sequence will infinitely pol for any DUT requests detected by
// the monitor, and trigger the response driver anytime a request is detected.

class csrng_device_seq extends csrng_base_seq;

  `uvm_object_utils(csrng_device_seq)
  `uvm_object_new

  csrng_item   req_q[$];
  push_pull_host_seq#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)   m_genbits_seq;

  virtual task body();
    fork
      forever begin
        csrng_item   req;
        p_sequencer.cmd_req_fifo.get(req);
        req_q.push_back(req);
      end

      forever begin
        csrng_item   rsp;
        wait(req_q.size);
        rsp = req_q.pop_front();
        case (rsp.acmd)
          GEN: begin
            m_genbits_seq = push_pull_host_seq#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)::type_id::
                create("m_genbits_seq");
            cfg.m_genbits_push_agent_cfg.host_delay_min = cfg.min_genbits_dly;
            cfg.m_genbits_push_agent_cfg.host_delay_max = cfg.max_genbits_dly;
            // TODO: randomize genbits
            cfg.m_genbits_push_agent_cfg.add_h_user_data(32'hdeadbeef);
            m_genbits_seq.start(p_sequencer.m_genbits_push_sequencer);
          end
        endcase
        start_item(rsp);
        finish_item(rsp);
      end
    join
  endtask

endclass
