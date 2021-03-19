// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// extend tl_seq_item to return a|d_user data with ECC value
class cip_tl_seq_item extends tl_seq_item;

  `uvm_object_utils_begin(cip_tl_seq_item)
  `uvm_object_utils_end

  `uvm_object_new

  function void post_randomize();
    a_user = get_a_user_val();
    d_user = get_d_user_val();
  endfunction

  // calculate ecc value for a_user
  virtual function tl_a_user_t get_a_user_val();
    tl_a_user_t user;
    tl_h2d_cmd_intg_t cmd_intg_payload;
    logic [H2DCmdFullWidth - 1 : 0] payload_intg;
    logic [D2HRspFullWidth - 1 : 0] data_intg;

    // construct command integrity
    cmd_intg_payload.tl_type = DataType;
    cmd_intg_payload.addr = a_addr;
    cmd_intg_payload.opcode = tl_a_op_e'(a_opcode);
    cmd_intg_payload.mask = a_mask;
    payload_intg = prim_secded_pkg::prim_secded_64_57_enc(H2DCmdMaxWidth'(cmd_intg_payload));

    // construct data integrity
    data_intg = prim_secded_pkg::prim_secded_64_57_enc(DataMaxWidth'(a_data));

    user.rsvd = '0;
    user.tl_type = DataType;
    user.cmd_intg = payload_intg[H2DCmdFullWidth -1 -: H2DCmdIntgWidth];
    user.data_intg = data_intg[DataFullWidth -1 -: DataIntgWidth];;
    return user;
  endfunction // get_a_user_val

  // device facing version of the function above
  virtual function tl_d_user_t get_d_user_val();
    tl_d_user_t user;
    tl_d2h_rsp_intg_t rsp_intg_payload;
    logic [D2HRspFullWidth - 1:0] payload_intg;
    logic [D2HRspFullWidth - 1:0] data_intg;

    // construct response integrity
    rsp_intg_payload.opcode = tl_d_op_e'(d_opcode);
    rsp_intg_payload.size = d_size;
    rsp_intg_payload.error = d_error;
    payload_intg = prim_secded_pkg::prim_secded_64_57_enc(D2HRspMaxWidth'(rsp_intg_payload));

    // construct data integrity
    data_intg = prim_secded_pkg::prim_secded_64_57_enc(DataMaxWidth'(d_data));

    user.rsp_intg = payload_intg[D2HRspFullWidth -1 -: D2HRspIntgWidth];
    user.data_intg = data_intg[DataFullWidth -1 -: DataIntgWidth];
    return user;
  endfunction // get_d_user_val

endclass
