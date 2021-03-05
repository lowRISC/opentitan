// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink sequence item
// ---------------------------------------------

// use macro to write constraint in order to reuse in functions:
// get_exp_d_error and randomize_a_chan_with_protocol_error
`define chk_prot_a_opcode \
  a_opcode inside {Get, PutFullData, PutPartialData}

// For PutFullData message, mask needs to match with size
`define chk_prot_mask_w_PutFullData \
  a_opcode != PutFullData || $countones(a_mask) == (1 << a_size)

// mask must align with addr, same as below
//   a_addr[1:0] == 1 -> a_mask[0]   == 0;
//   a_addr[1:0] == 2 -> a_mask[1:0] == 0;
//   a_addr[1:0] == 3 -> a_mask[2:0] == 0;
`define chk_prot_addr_mask_align \
  MaskWidth'(a_mask << (4 - a_addr[SizeWidth-1:0])) == 0

// mask must be within enabled lanes
// prevent cases: addr: 0h, size: 1, mask: 'b1100; addr: 0h, size: 0, mask: 'b1000
`define chk_prot_mask_in_enabled_lanes \
  ((a_mask >> a_addr[SizeWidth-1:0]) >> (1 << a_size)) == 0

// Address must be aligned to the a_size (2 ** a_size bytes)
`define chk_prot_addr_size_align \
  (a_addr << (AddrWidth - a_size)) == 0

// max size is 2
`define chk_prot_max_size \
  a_size <= 2

class tl_seq_item extends uvm_sequence_item;

  rand bit [AddrWidth - 1   : 0] a_addr;
  rand bit [DataWidth - 1   : 0] a_data;
  rand bit [MaskWidth - 1   : 0] a_mask;
  rand bit [SizeWidth - 1   : 0] a_size;
  rand bit [2:0]                 a_param;
  rand bit [SourceWidth - 1 : 0] a_source;
  rand bit [OpcodeWidth - 1 : 0] a_opcode;

  rand bit [2:0]                 d_param;
  rand bit [DataWidth - 1   : 0] d_data;
  rand bit [SourceWidth - 1 : 0] d_source;
  rand bit [SizeWidth - 1   : 0] d_size;
  rand bit [OpcodeWidth - 1 : 0] d_opcode;
  rand bit                       d_error;
  rand bit [DUserWidth - 1 : 0]  d_user;
  rand bit                       d_sink;

  // host mode delays
  rand int unsigned               a_valid_delay;
  rand int unsigned               a_valid_len;

  // device mode delays
  rand int unsigned               d_valid_delay;
  rand int unsigned               d_valid_len;

  // Indicates a_source val is overridden.
  //
  // a_source is randomized and set in tl_host_base_seq::finish_item() to facilitate late
  // randomization. If this bit is set, the a_source is assumed to be set to a fixed value instead.
  // It is possible that this fixed value might match one of the pending reqs in the that has not
  // yet completed. The driver can then use this bit to add more delays if needed before sending
  // this request, to avoid protocol violation.
  bit                             a_source_is_overridden;

  // after given valid_len, end the req/rsp if it's not accepted, which allows seq to switch
  // content and test unaccepted item shouldn't be used in design
  bit                             req_abort_after_a_valid_len;
  bit                             rsp_abort_after_d_valid_len;
  // True if the item is completed, not aborted
  bit                             req_completed;
  bit                             rsp_completed;

  // param is reserved for future use, must be zero
  constraint param_c {
    a_param == 0;
    d_param == 0;
  }

  constraint no_d_error_c {
    soft d_error == 0;
  }

  constraint a_valid_len_c {
    soft a_valid_len inside {[1:10]};
  }

  constraint d_valid_len_c {
    soft d_valid_len inside {[1:10]};
  }

  constraint valid_delay_c {
    soft a_valid_delay inside {[0:50]};
    soft d_valid_delay inside {[0:50]};
  }

  constraint d_opcode_c {
    d_opcode inside {AccessAckData, AccessAck};
  }

  constraint a_opcode_c {
    `chk_prot_a_opcode;
  }

  // mask must be contiguous, e.g. 'b1001, 'b1010 aren't allowed
  constraint mask_contiguous_c {
    $countones(a_mask ^ {a_mask[MaskWidth-2:0], 1'b0}) <= 2;
  }

  constraint mask_w_PutFullData_c {
    `chk_prot_mask_w_PutFullData;
  }

  constraint addr_mask_align_c {
    `chk_prot_addr_mask_align;
  }

  constraint mask_in_enabled_lanes_c {
    `chk_prot_mask_in_enabled_lanes;
  }

  constraint addr_size_align_c {
    `chk_prot_addr_size_align;
  }

  // size can't be more than 2
  constraint max_size_c {
    `chk_prot_max_size;
  }

  `uvm_object_utils_begin(tl_seq_item)
    `uvm_field_int  (a_addr,              UVM_DEFAULT)
    `uvm_field_int  (a_data,              UVM_DEFAULT)
    `uvm_field_int  (a_mask,              UVM_DEFAULT)
    `uvm_field_int  (a_size,              UVM_DEFAULT)
    `uvm_field_int  (a_param,             UVM_DEFAULT)
    `uvm_field_int  (a_source,            UVM_DEFAULT)
    `uvm_field_int  (a_opcode,            UVM_DEFAULT)
    `uvm_field_int  (d_param,             UVM_DEFAULT)
    `uvm_field_int  (d_source,            UVM_DEFAULT)
    `uvm_field_int  (d_data,              UVM_DEFAULT)
    `uvm_field_int  (d_size,              UVM_DEFAULT)
    `uvm_field_int  (d_opcode,            UVM_DEFAULT)
    `uvm_field_int  (d_error,             UVM_DEFAULT)
    `uvm_field_int  (d_sink,              UVM_DEFAULT)
    `uvm_field_int  (d_user,              UVM_DEFAULT)
    `uvm_field_int  (a_source_is_overridden, UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (a_valid_delay,       UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (d_valid_delay,       UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (a_valid_len,         UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (d_valid_len,         UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (req_abort_after_a_valid_len, UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (rsp_abort_after_d_valid_len, UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (req_completed,       UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (rsp_completed,       UVM_DEFAULT | UVM_NOPACK)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
  endfunction : new

  virtual function string convert2string();
    string str;
    string a_opcode_name, d_opcode_name;
    tl_a_op_e a_op_e;
    tl_d_op_e d_op_e;
    if ($cast(a_op_e, a_opcode)) a_opcode_name = a_op_e.name();
    else                         a_opcode_name = $sformatf("Invalid, value: %0d", a_opcode);
    if ($cast(d_op_e, d_opcode)) d_opcode_name = d_op_e.name();
    else                         d_opcode_name = $sformatf("Invalid, value: %0d", d_opcode);

    str = {$sformatf("a_addr = 0x%0h ", a_addr),
           $sformatf("a_data = 0x%0h ", a_data),
           $sformatf("a_mask = 0x%0h ", a_mask),
           $sformatf("a_size = 0x%0h ", a_size),
           $sformatf("a_param = 0x%0h ", a_param),
           $sformatf("a_source = 0x%0h ", a_source),
           $sformatf("a_opcode = %0s ", a_opcode_name),
           $sformatf("d_data = 0x%0h ", d_data),
           $sformatf("d_size = 0x%0h ", d_size),
           $sformatf("d_param = 0x%0h ", d_param),
           $sformatf("d_source = 0x%0h ", d_source),
           $sformatf("d_opcode = %0s ", d_opcode_name),
           $sformatf("d_error = %0b ", d_error),
           $sformatf("d_user = %0b ", d_user),
           $sformatf("d_sink = %0b ", d_sink),
           $sformatf("req_abort_after_a_valid_len = %0b ", req_abort_after_a_valid_len),
           $sformatf("rsp_abort_after_d_valid_len = %0b ", rsp_abort_after_d_valid_len),
           $sformatf("req_completed = %0b ", req_completed),
           $sformatf("rsp_completed = %0b ", rsp_completed)};
    return str;
  endfunction

  function void disable_a_chan_randomization();
    a_addr.rand_mode(0);
    a_data.rand_mode(0);
    a_mask.rand_mode(0);
    a_size.rand_mode(0);
    a_param.rand_mode(0);
    a_source.rand_mode(0);
    a_opcode.rand_mode(0);
  endfunction

  // calculate d_error based on values of a_chan
  function bit get_exp_d_error();
    return get_error_a_opcode_invalid() || get_error_PutFullData_mask_size_mismatched() ||
           get_error_addr_mask_misaligned() || get_error_addr_size_misaligned() ||
           get_error_mask_not_in_enabled_lanes() || get_error_size_over_max();
  endfunction

  function bit get_error_a_opcode_invalid();
    return !(`chk_prot_a_opcode);
  endfunction

  function bit get_error_PutFullData_mask_size_mismatched();
    return !(`chk_prot_mask_w_PutFullData);
  endfunction

  function bit get_error_addr_mask_misaligned();
    return !(`chk_prot_addr_mask_align);
  endfunction

  function bit get_error_addr_size_misaligned();
    return !(`chk_prot_addr_size_align);
  endfunction

  function bit get_error_mask_not_in_enabled_lanes();
    return !(`chk_prot_mask_in_enabled_lanes);
  endfunction

  function bit get_error_size_over_max();
    return !(`chk_prot_max_size);
  endfunction // get_error_size_over_max

  // Calling secded 64_57 directly does not seem great...
  // Temporary solution to get dv going
  virtual function tl_a_user_t get_a_user_val();
    tl_a_user_t user;
    tl_h2d_cmd_intg_t cmd_intg_payload;
    logic [H2DCmdFullWidth - 1:0] payload_intg;
    logic [D2HRspFullWidth - 1:0] data_intg;

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



  function void disable_a_chan_protocol_constraint();
    a_opcode_c.constraint_mode(0);
    mask_contiguous_c.constraint_mode(0);
    mask_w_PutFullData_c.constraint_mode(0);
    addr_mask_align_c.constraint_mode(0);
    mask_in_enabled_lanes_c.constraint_mode(0);
    addr_size_align_c.constraint_mode(0);
    max_size_c.constraint_mode(0);
  endfunction

  // randomly disable constraint_mode for a chan
  // at least one constraint_mode needs to be disabled to make sure protocol is violated
  function void randomize_a_chan_with_protocol_error();
    bit cm_a_opcode, cm_mask_w_PutFullData;
    bit cm_addr_mask_align, cm_mask_in_enabled_lanes, cm_addr_size_align, cm_max_size;
    `DV_CHECK_FATAL(std::randomize(cm_a_opcode, cm_mask_w_PutFullData,
                                   cm_addr_mask_align, cm_mask_in_enabled_lanes,
                                   cm_addr_size_align, cm_max_size) with {
                                   // at least one constraint_mode is off
                                   !(cm_a_opcode && cm_mask_w_PutFullData &&
                                   cm_addr_mask_align && cm_mask_in_enabled_lanes &&
                                   cm_addr_size_align && cm_max_size);
                                   })
    a_opcode_c.constraint_mode(cm_a_opcode);
    mask_w_PutFullData_c.constraint_mode(cm_mask_w_PutFullData);
    addr_mask_align_c.constraint_mode(cm_addr_mask_align);
    mask_in_enabled_lanes_c.constraint_mode(cm_mask_in_enabled_lanes);
    addr_size_align_c.constraint_mode(cm_addr_size_align);
    max_size_c.constraint_mode(cm_max_size);
    `DV_CHECK_FATAL(
        // at least one `chk_prot_* is violated
        randomize() with {!cm_a_opcode              && !(`chk_prot_a_opcode)              ||
                          !cm_mask_w_PutFullData    && !(`chk_prot_mask_w_PutFullData)    ||
                          !cm_addr_mask_align       && !(`chk_prot_addr_mask_align)       ||
                          !cm_mask_in_enabled_lanes && !(`chk_prot_mask_in_enabled_lanes) ||
                          !cm_addr_size_align       && !(`chk_prot_addr_size_align)       ||
                          !cm_max_size              && !(`chk_prot_max_size);})
  endfunction

  // Find whether this seq item is a read or a write.
  virtual function bit is_write();
    return (a_opcode inside {PutFullData, PutPartialData});
  endfunction

  // Check if d_opcode is appropriate for the given a_opcode. This check assumes that the
  // response packet has been appended with the corresponding request.
  virtual function bit check_opcodes(bit throw_error = 1'b1);
    // for read, return AccessAckData; for write or error opcode, return AccessAck
    tl_d_op_e exp_d_opcode = a_opcode == Get ? tlul_pkg::AccessAckData : tlul_pkg::AccessAck;
    check_opcodes = (d_opcode == int'(exp_d_opcode));
    if (!check_opcodes && throw_error) begin
      `uvm_error(`gfn, $sformatf("d_opcode: %0d & exp_d_opcode: %0d mismatch",
                                  d_opcode, exp_d_opcode))
    end
  endfunction

  // Check if packet parameters are ok.
  virtual function bit is_ok(bit throw_error = 1'b1);
    is_ok = 1'b1;
    is_ok &= check_opcodes(throw_error);
    // addr and data channels should have the same source
    is_ok &= (a_source == d_source);
    if (!is_ok && throw_error)
      `uvm_error(`gfn, $sformatf("a_source: 0x%0h & d_source: 0x%0h mismatch", a_source, d_source))
  endfunction

endclass

`undef chk_prot_a_opcode
`undef chk_prot_mask_w_PutFullData
`undef chk_prot_addr_mask_align
`undef chk_prot_mask_in_enabled_lanes
`undef chk_prot_addr_size_align
`undef chk_prot_max_size
