// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_tl_device_seq extends cip_tl_device_seq;

  `uvm_object_utils(mbx_tl_device_seq)

  `uvm_object_new

  virtual function void update_mem(REQ rsp);
    super.update_mem(rsp);
    rsp.d_user = rsp.compute_d_user();
    if (inject_d_chan_intg_err) begin
      rsp.tl_intg_err_type = tl_intg_err_type;
      rsp.inject_d_chan_intg_err();
    end
  endfunction: update_mem

endclass: mbx_tl_device_seq
