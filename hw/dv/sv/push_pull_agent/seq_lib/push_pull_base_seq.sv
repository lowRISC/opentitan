// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_base_seq #(parameter int HostDataWidth = 32,
                           parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_seq #(
    .REQ         (push_pull_item#(HostDataWidth, DeviceDataWidth)),
    .CFG_T       (push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth)),
    .SEQUENCER_T (push_pull_sequencer#(HostDataWidth, DeviceDataWidth))
  );
  `uvm_object_param_utils(push_pull_base_seq#(HostDataWidth, DeviceDataWidth))

  `uvm_object_new

  // Randomizes the req or response.
  //
  // Regardless of agent or item type, we can apply the same set of limits.
  virtual function void randomize_item(push_pull_item #(HostDataWidth, DeviceDataWidth) item);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(item,
      if (cfg.zero_delays) {
        host_delay == 0;
        device_delay == 0;
        req_lo_delay == 0;
        ack_lo_delay == 0;
      } else {
        host_delay inside {[cfg.host_delay_min : cfg.host_delay_max]};
        device_delay inside {[cfg.device_delay_min : cfg.device_delay_max]};
        req_lo_delay inside {[cfg.req_lo_delay_min : cfg.req_lo_delay_max]};
        ack_lo_delay inside {[cfg.ack_lo_delay_min : cfg.ack_lo_delay_max]};
      }
    )
  endfunction

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
