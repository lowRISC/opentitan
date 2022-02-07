// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Response sequence for csrng protocols.
// This sequence will infinitely pol for any DUT requests detected by
// the monitor, and trigger the response driver anytime a request is detected.

class csrng_device_seq extends csrng_base_seq;

  `uvm_object_utils(csrng_device_seq)
  `uvm_object_new

  push_pull_host_seq#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)   m_genbits_seq;

  virtual task body();
    forever begin
      csrng_item   req;

      p_sequencer.req_analysis_fifo.get(req);
      `uvm_info(`gfn, $sformatf("Received item: %s", req.convert2string()), UVM_HIGH)
      cfg.m_cmd_push_agent_cfg.zero_delays = cfg.cmd_ack_zero_delays;
      if (req.acmd == csrng_pkg::GEN) begin
        m_genbits_seq = push_pull_host_seq#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)::type_id::
           create("m_genbits_seq");
        cfg.m_genbits_push_agent_cfg.host_delay_min = cfg.min_genbits_dly;
        cfg.m_genbits_push_agent_cfg.host_delay_max = cfg.max_genbits_dly;
        m_genbits_seq.num_trans = req.glen;
        m_genbits_seq.start(p_sequencer.m_genbits_push_sequencer);
      end
      start_item(req);
      finish_item(req);
      get_response(rsp);
    end
  endtask

endclass
