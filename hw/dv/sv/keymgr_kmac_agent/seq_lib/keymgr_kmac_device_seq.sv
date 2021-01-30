// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_device_seq extends keymgr_kmac_base_seq;
  `uvm_object_utils(keymgr_kmac_device_seq)
  `uvm_object_new

  virtual task body();
    forever begin
      p_sequencer.req_data_fifo.get(req);
      $cast(rsp, req.clone());
      start_item(rsp);
      randomize_item(rsp);
      finish_item(rsp);
      get_response(rsp);
      `uvm_info(`gfn, $sformatf("Sent response: %0s", rsp.sprint()), UVM_HIGH)
    end
  endtask

  virtual function void randomize_item(REQ item);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(item,
      if (cfg.zero_delays) {
        rsp_delay == 0;
      } else {
        rsp_delay inside {[cfg.rsp_delay_min : cfg.rsp_delay_max]};
      }
      is_kmac_rsp_err dist {1 :/ cfg.error_rsp_pct,
                            0 :/ 100 - cfg.error_rsp_pct};
    )
  endfunction
endclass
