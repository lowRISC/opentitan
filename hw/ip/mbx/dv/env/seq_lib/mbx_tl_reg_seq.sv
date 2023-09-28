// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_tl_reg_seq extends cip_tl_host_single_seq;

  rand tlul_pkg::tl_a_user_t auser;

  `uvm_object_utils(mbx_tl_reg_seq)

  constraint size_c { size == 2; }
  constraint mask_c { mask == 'hf; }
  constraint auser_c { auser.instr_type == prim_mubi_pkg::MuBi4False; }

  function new (string name = "");
    super.new(name);
  endfunction: new

  virtual function void randomize_req(REQ req, int idx);
    control_rand_size = 1;
    control_rand_opcode = 1;
    super.randomize_req(req, idx);
    req.a_user = auser;
  endfunction

endclass: mbx_tl_reg_seq
