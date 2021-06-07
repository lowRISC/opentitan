// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// extend tl_seq_item to return a|d_user data with ECC value
class cip_tl_seq_item extends tl_seq_item;

  `uvm_object_utils_begin(cip_tl_seq_item)
  `uvm_object_utils_end

  `uvm_object_new

  tlul_pkg::tl_type_e tl_type = DataType;
  tl_intg_err_e       tl_intg_err_type = TlIntgErrNone;
  // the max errors that we can detect
  int                 max_ecc_errors = 3;

  function void post_randomize();
    update_a_chan_intg_val(tl_intg_err_type);
  endfunction

  // calculate ecc value for a_user
  virtual function tl_a_user_t get_a_user_val();
    tl_a_user_t user;
    tl_h2d_cmd_intg_t cmd_intg_payload;
    logic [H2DCmdFullWidth - 1 : 0] cmd_with_intg;
    logic [D2HRspFullWidth - 1 : 0] data_with_intg;

    // construct command integrity
    cmd_intg_payload.tl_type = tl_type;
    cmd_intg_payload.addr = a_addr;
    cmd_intg_payload.opcode = tl_a_op_e'(a_opcode);
    cmd_intg_payload.mask = a_mask;
    cmd_with_intg = prim_secded_pkg::prim_secded_64_57_enc(H2DCmdMaxWidth'(cmd_intg_payload));

    // construct data integrity
    data_with_intg = prim_secded_pkg::prim_secded_64_57_enc(DataMaxWidth'(a_data));

    user.rsvd = '0;
    user.tl_type = tl_type;
    user.cmd_intg = cmd_with_intg[H2DCmdFullWidth -1 -: H2DCmdIntgWidth];
    user.data_intg = data_with_intg[DataFullWidth -1 -: DataIntgWidth];;
    return user;
  endfunction // get_a_user_val

  // device facing version of the function above
  virtual function tl_d_user_t get_d_user_val();
    tl_d_user_t user;
    tl_d2h_rsp_intg_t rsp_intg_payload;
    logic [D2HRspFullWidth - 1:0] rsp_with_intg;
    logic [D2HRspFullWidth - 1:0] data_with_intg;

    // construct response integrity
    rsp_intg_payload.opcode = tl_d_op_e'(d_opcode);
    rsp_intg_payload.size = d_size;
    rsp_intg_payload.error = d_error;
    rsp_with_intg = prim_secded_pkg::prim_secded_64_57_enc(D2HRspMaxWidth'(rsp_intg_payload));

    // construct data integrity
    data_with_intg = prim_secded_pkg::prim_secded_64_57_enc(DataMaxWidth'(d_data));

    user.rsp_intg = rsp_with_intg[D2HRspFullWidth -1 -: D2HRspIntgWidth];
    user.data_intg = data_with_intg[DataFullWidth -1 -: DataIntgWidth];
    return user;
  endfunction // get_d_user_val

  // update data and ecc value for a channel
  virtual function void update_a_chan_intg_val(tl_intg_err_e tl_intg_err_type = TlIntgErrNone);
    tl_a_user_t cur_user = get_a_user_val();
    tl_a_user_t final_user;
    cip_tl_seq_item cur_item;
    bit [DataIntgWidth + $bits(tl_h2d_cmd_intg_t) - 1 : 0] cmd_and_intg_err_mask;
    bit [DataIntgWidth + BUS_DW - 1 : 0]                   data_and_intg_err_mask;

    `downcast(cur_item, this.clone())

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cmd_and_intg_err_mask,
        if (tl_intg_err_type inside {TlIntgErrCmd, TlIntgErrBoth}) {
          $countones(cmd_and_intg_err_mask) inside {[1 : max_ecc_errors]};
        } else {
          cmd_and_intg_err_mask == '0;
        })
    {a_addr, a_opcode, a_mask, final_user.tl_type, final_user.cmd_intg} = {
        cur_item.a_addr,
        cur_item.a_opcode,
        cur_item.a_mask,
        cur_user.tl_type,
        cur_user.cmd_intg} ^ cmd_and_intg_err_mask;

    if (cmd_and_intg_err_mask != '0) begin
      string str = "TL cmd or integrity bits have been flipped, see the changes as below:\n";
      str = $sformatf("%s\t a_addr: 0x%0x -> 0x%0x\n", str, cur_item.a_addr, a_addr);
      str = $sformatf("%s\t a_opcode: 0x%0x -> 0x%0x\n", str, cur_item.a_opcode, a_opcode);
      str = $sformatf("%s\t a_mask: 0x%0x -> 0x%0x\n", str, cur_item.a_mask, a_mask);
      str = $sformatf("%s\t tl_type: 0x%0x -> 0x%0x\n", str, cur_user.tl_type, final_user.tl_type);
      str = $sformatf("%s\t cmd_intg: 0x%0x -> 0x%0x\n", str, cur_user.cmd_intg,
                      final_user.cmd_intg);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_and_intg_err_mask,
        if (tl_intg_err_type inside {TlIntgErrData, TlIntgErrBoth}) {
          $countones(data_and_intg_err_mask) inside {[1 : max_ecc_errors]};
        } else {
          data_and_intg_err_mask == '0;
        })
    {a_data, final_user.data_intg} = {cur_item.a_data, final_user.data_intg} ^
                                     data_and_intg_err_mask;

    if (cmd_and_intg_err_mask != '0) begin
      string str = "TL data or integrity bits have been flipped, see the changes as below: \n";
      str = $sformatf("%s\t a_data: 0x%0x -> 0x%0x\n", str, cur_item.a_data, a_data);
      str = $sformatf("%s\t data_intg: 0x%0x -> 0x%0x\n", str, cur_user.data_intg,
                      final_user.data_intg);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    a_user = final_user;
  endfunction // update_a_chan_intg_val

  // update data and ecc value for d channel
  virtual function void update_d_chan_intg_val(tl_intg_err_e tl_intg_err_type = TlIntgErrNone);
    tl_d_user_t cur_user = get_d_user_val();
    tl_d_user_t final_user;
    cip_tl_seq_item cur_item;
    bit [DataIntgWidth + $bits(tl_d2h_rsp_intg_t) - 1 : 0] rsp_and_intg_err_mask;
    bit [DataIntgWidth + BUS_DW - 1 : 0]                   data_and_intg_err_mask;

    `downcast(cur_item, this.clone())

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(rsp_and_intg_err_mask,
        if (tl_intg_err_type inside {TlIntgErrCmd, TlIntgErrBoth}) {
          $countones(rsp_and_intg_err_mask) inside {[1 : max_ecc_errors]};
        } else {
          rsp_and_intg_err_mask == '0;
        })
    {d_opcode, d_size, d_error, final_user.rsp_intg} = {
        cur_item.d_opcode,
        cur_item.d_size,
        cur_item.d_error,
        cur_user.rsp_intg} ^ rsp_and_intg_err_mask;

    if (rsp_and_intg_err_mask != '0) begin
      string str = "TL cmd or integrity bits have been flipped, see the changes as below:\n";
      str = $sformatf("%s\t d_opcode: 0x%0x -> 0x%0x\n", str, cur_item.d_opcode, d_opcode);
      str = $sformatf("%s\t d_size: 0x%0x -> 0x%0x\n", str, cur_item.d_size, d_size);
      str = $sformatf("%s\t d_error: 0x%0x -> 0x%0x\n", str, cur_item.d_error, d_error);
      str = $sformatf("%s\t rsp_intg: 0x%0x -> 0x%0x\n", str, cur_user.rsp_intg,
                      final_user.rsp_intg);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_and_intg_err_mask,
        if (tl_intg_err_type inside {TlIntgErrData, TlIntgErrBoth}) {
          $countones(data_and_intg_err_mask) inside {[1 : max_ecc_errors]};
        } else {
          data_and_intg_err_mask == '0;
        })
    {a_data, final_user.data_intg} = {cur_item.a_data, final_user.data_intg} ^
                                     data_and_intg_err_mask;

    if (rsp_and_intg_err_mask != '0) begin
      string str = "TL data or integrity bits have been flipped, see the changes as below: \n";
      str = $sformatf("%s\t a_data: 0x%0x -> 0x%0x\n", str, cur_item.a_data, a_data);
      str = $sformatf("%s\t data_intg: 0x%0x -> 0x%0x\n", str, cur_user.data_intg,
                      final_user.data_intg);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    d_user = final_user;
  endfunction // update_d_chan_intg_val

  virtual function bit is_a_user_ok(bit throw_error = 1'b1);
    tl_a_user_t exp_user = get_a_user_val();
    tl_a_user_t act_user = tl_a_user_t'(a_user);

    // TODO, #6887, dat_intg isn't implemented in design
    // is_a_user_ok = (act_user.cmd_intg == exp_user.cmd_intg) &&
    //                (act_user.data_intg == exp_user.data_intg);
    is_a_user_ok = (act_user.cmd_intg == exp_user.cmd_intg);

    if (!is_a_user_ok) begin
      `uvm_info(`gfn, $sformatf(
                "cmd_intg act (0x%0x) != exp (0x%0x), data_intg act (0x%0x) != exp (0x%0x)",
                act_user.cmd_intg, exp_user.cmd_intg, act_user.data_intg, exp_user.data_intg),
                UVM_LOW)
    end
    if (!is_a_user_ok && throw_error) begin
      `uvm_error(`gfn, "a_user integrity check fails")
    end
  endfunction // is_a_user_ok

endclass
