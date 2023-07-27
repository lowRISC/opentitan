// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_pull_seq extends tl_device_seq;

  `uvm_object_utils(dma_pull_seq)

  function new (string name = "dma_pull_seq");
    super.new(name);
    min_rsp_delay = 1;
    max_rsp_delay = 4;
  endfunction: new

  virtual function void update_mem(REQ rsp);
    bit [65:0] intg;

    super.update_mem(rsp);
    intg = prim_secded_pkg::prim_secded_inv_64_57_enc({51'b0,
                                                       rsp.d_opcode,
                                                       rsp.d_size,
                                                       rsp.d_error});
    rsp.d_user[13:7] = intg[63:57];
  endfunction: update_mem

  virtual function void randomize_rsp(REQ rsp);
    rsp.disable_a_chan_randomization();
    if (d_error_pct > 0) rsp.no_d_error_c.constraint_mode(0);
    if (!(rsp.randomize() with
           {rsp.d_valid_delay inside {[min_rsp_delay : max_rsp_delay]};
            if (rsp.a_opcode == tlul_pkg::Get) {
              rsp.d_opcode == tlul_pkg::AccessAckData;
            } else {
              rsp.d_opcode == tlul_pkg::AccessAck;
            }
            rsp.d_size == rsp.a_size;
            rsp.d_source == rsp.a_source;
            d_error dist {0 :/ (100 - d_error_pct), 1 :/ d_error_pct};
        })) begin
      `uvm_fatal(`gfn, "Cannot randomize rsp")
    end
    `uvm_info("dma_pull_seq",
              $sformatf("[check][d_chan] : a_address=0x%08h d_valid_delay=%0d",
                        rsp.a_addr, rsp.d_valid_delay),
              UVM_HIGH)
  endfunction
endclass
