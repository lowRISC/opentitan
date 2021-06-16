// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// extend tl_seq_item to return a|d_user data with ECC value
class cip_tl_seq_item extends tl_seq_item;

  `uvm_object_new

  tlul_pkg::tl_type_e tl_type = DataType;
  tl_intg_err_e       tl_intg_err_type = TlIntgErrNone;
  // the max errors that we can detect
  int                 max_ecc_errors = MAX_TL_ECC_ERRORS;

  `uvm_object_utils_begin(cip_tl_seq_item)
    `uvm_field_enum(tlul_pkg::tl_type_e, tl_type,          UVM_DEFAULT)
    `uvm_field_enum(tl_intg_err_e,       tl_intg_err_type, UVM_DEFAULT)
    `uvm_field_int(max_ecc_errors,                         UVM_DEFAULT)
  `uvm_object_utils_end

  function void post_randomize();
    a_user = compute_a_user();
    inject_a_chan_intg_err();
  endfunction

  // calculate ecc value for a_user and return a_user
  // class member a_user isn't updated in this function
  virtual function tl_a_user_t compute_a_user();
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
    user.data_intg = data_with_intg[DataFullWidth -1 -: DataIntgWidth];
    return user;
  endfunction : compute_a_user

  // device facing version of the function above
  virtual function tl_d_user_t compute_d_user();
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
  endfunction : compute_d_user

  // update data and ecc value for a channel
  virtual function void inject_a_chan_intg_err();
    // define a struct type local a_user to access ECC or other field easily
    tl_a_user_t l_a_user = tl_a_user_t'(a_user);

    if (tl_intg_err_type == TlIntgErrNone) return;

    if (tl_intg_err_type inside {TlIntgErrCmd, TlIntgErrBoth}) begin
      bit [DataIntgWidth + $bits(tl_h2d_cmd_intg_t) - 1 : 0] cmd_and_intg_err_mask;
      // Pre-populate str with format specifiers for the updated values that will be set later.
      string str = {"TL data or integrity bits have been flipped, see the changes as below:\n",
                   $sformatf("\t a_addr: 0x%0x\n", a_addr), " -> 0x%0x",
                   $sformatf("\t a_opcode: 0x%0x\n", a_opcode), " -> 0x%0x",
                   $sformatf("\t a_mask: 0x%0x\n", a_mask), " -> 0x%0x",
                   $sformatf("\t tl_type: 0x%0x\n", l_a_user.tl_type), " -> 0x%0x",
                   $sformatf("\t cmd_intg: 0x%0x\n", l_a_user.cmd_intg), " -> 0x%0x"};

      // Flip cmd or intg ecc
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cmd_and_intg_err_mask,
          $countones(cmd_and_intg_err_mask) inside {[1 : max_ecc_errors]};)
      {a_addr, a_opcode, a_mask, l_a_user.tl_type, l_a_user.cmd_intg} ^= cmd_and_intg_err_mask;

      str = $sformatf(str, a_addr, a_opcode, a_mask, l_a_user.tl_type, l_a_user.cmd_intg);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    if (tl_intg_err_type inside {TlIntgErrData, TlIntgErrBoth}) begin
      bit [DataIntgWidth + BUS_DW - 1 : 0] data_and_intg_err_mask;
      // Pre-populate str with format specifiers for the updated values that will be set later.
      string str = {"TL data or integrity bits have been flipped, see the changes as below:\n",
                   $sformatf("\t a_data: 0x%0x\n", a_data), " -> 0x%0x"};

      // Flip data or intg ecc
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_and_intg_err_mask,
          $countones(data_and_intg_err_mask) inside {[1 : max_ecc_errors]};)
      {a_data, l_a_user.data_intg} ^= data_and_intg_err_mask;

      str = $sformatf(str, a_data);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    a_user = l_a_user;
  endfunction : inject_a_chan_intg_err

  // update data and ecc value for d channel
  virtual function void inject_d_chan_intg_err();
    // define a struct type local d_user to access ECC or other field easily
    tl_d_user_t l_d_user = tl_d_user_t'(d_user);

    if (tl_intg_err_type == TlIntgErrNone) return;

    if (tl_intg_err_type inside {TlIntgErrCmd, TlIntgErrBoth}) begin
      bit [DataIntgWidth + $bits(tl_d2h_rsp_intg_t) - 1 : 0] rsp_and_intg_err_mask;
      // Pre-populate str with format specifiers for the updated values that will be set later.
      string str = {"TL data or integrity bits have been flipped, see the changes as below:\n",
                   $sformatf("\t d_opcode: 0x%0x\n", d_opcode), " -> 0x%0x",
                   $sformatf("\t d_size: 0x%0x\n", d_size), " -> 0x%0x",
                   $sformatf("\t d_error: 0x%0x\n", d_error), " -> 0x%0x",
                   $sformatf("\t rsp_intg: 0x%0x\n", l_d_user.rsp_intg), " -> 0x%0x"};

    // Flip cmd or intg ecc
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(rsp_and_intg_err_mask,
        $countones(rsp_and_intg_err_mask) inside {[1 : max_ecc_errors]};)
    {d_opcode, d_size, d_error, l_d_user.rsp_intg} ^= rsp_and_intg_err_mask;

      str = $sformatf(str, d_opcode, d_size, d_error, l_d_user.rsp_intg);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    if (tl_intg_err_type inside {TlIntgErrData, TlIntgErrBoth}) begin
      bit [DataIntgWidth + BUS_DW - 1 : 0] data_and_intg_err_mask;
      // Pre-populate str with format specifiers for the updated values that will be set later.
      string str = {"TL data or integrity bits have been flipped, see the changes as below:\n",
                   $sformatf("\t a_data: 0x%0x\n", d_data), " -> 0x%0x"};

      // Flip data or intg ecc
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_and_intg_err_mask,
          $countones(data_and_intg_err_mask) inside {[1 : max_ecc_errors]};)
      {d_data, l_d_user.data_intg} ^= data_and_intg_err_mask;

      str = $sformatf(str, d_data);
      `uvm_info(`gfn, str, UVM_LOW)
    end

    d_user = l_d_user;
  endfunction : inject_d_chan_intg_err

  virtual function bit is_a_chan_intg_ok(bit throw_error = 1'b1);
    tl_a_user_t exp_a_user = compute_a_user();
    tl_a_user_t act_a_user = tl_a_user_t'(a_user);

    // TODO, #6887, dat_intg isn't implemented in design
    // is_a_chan_intg_ok = act_a_user == exp_a_user;
    is_a_chan_intg_ok = (act_a_user.cmd_intg == exp_a_user.cmd_intg);

    if (!is_a_chan_intg_ok) begin
      string str = $sformatf("cmd_intg act (%p) != exp (%p)", act_a_user, exp_a_user);
      if (throw_error) begin
        `uvm_error(`gfn, str)
      end else begin
        `uvm_info(`gfn, str, UVM_MEDIUM)
      end
    end
  endfunction : is_a_chan_intg_ok

endclass
