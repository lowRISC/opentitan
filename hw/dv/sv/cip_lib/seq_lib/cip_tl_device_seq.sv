// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Extends the tl_device_seq to handle integrity of the response channel.
class cip_tl_device_seq extends tl_device_seq #(cip_tl_seq_item);

  `uvm_object_utils(cip_tl_device_seq)
  `uvm_object_new

  int d_chan_intg_err_pct = 0;

  rand bit inject_d_chan_intg_err;
  constraint inject_d_chan_intg_err_c {
    inject_d_chan_intg_err dist {
      1 :/ d_chan_intg_err_pct,
      0 :/ 100 - d_chan_intg_err_pct
    };
  }

  rand tl_intg_err_e tl_intg_err_type;
  constraint tl_intg_err_type_c {
    (d_chan_intg_err_pct > 0) -> (tl_intg_err_type != TlIntgErrNone);
  }

  virtual function void randomize_rsp(cip_tl_seq_item rsp);
    super.randomize_rsp(rsp);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(inject_d_chan_intg_err)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(tl_intg_err_type)
    rsp.d_user = rsp.compute_d_user();
    if (inject_d_chan_intg_err) begin
      rsp.tl_intg_err_type = tl_intg_err_type;
      rsp.inject_d_chan_intg_err();
    end
  endfunction

endclass
