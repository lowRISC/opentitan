// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_device_seq extends kmac_app_base_seq;
  `uvm_object_utils(kmac_app_device_seq)
  `uvm_object_new

  virtual task body();
    forever begin
      p_sequencer.req_analysis_fifo.get(req);
      $cast(rsp, req.clone());
      start_item(rsp);
      randomize_item(rsp);
      finish_item(rsp);
      get_response(rsp);
      `uvm_info(`gfn, $sformatf("Sent response: %0s", rsp.sprint()), UVM_HIGH)
    end
  endtask

  virtual function void randomize_item(REQ item);
    kmac_pkg::rsp_digest_t rsp_digest_h = '0;
    bit gen_error, set_share;

    if (cfg.has_user_digest_share()) begin
      set_share = 1;
      rsp_digest_h = cfg.get_user_digest_share();
    end else begin
      set_share = 0;
    end

    gen_error = $urandom_range(100, 1) <= cfg.error_rsp_pct;

    `DV_CHECK_RANDOMIZE_WITH_FATAL(item,
      if (cfg.zero_delays) {
        rsp_delay == 0;
      } else {
        rsp_delay inside {[cfg.rsp_delay_min : cfg.rsp_delay_max]};
      }
      if (set_share) {
        rsp_digest_share0 == rsp_digest_h.digest_share0;
        rsp_digest_share1 == rsp_digest_h.digest_share1;
      }
      gen_error == (rsp_error ||
                    (cfg.constant_share_means_error &&
                     (rsp_digest_share0 inside {'0, '1} || rsp_digest_share1 inside {'0, '1})));
    )
  endfunction

endclass
