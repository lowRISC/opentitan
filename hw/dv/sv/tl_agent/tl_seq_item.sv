// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink sequence item
// ---------------------------------------------

// An expression that is true if a_opcode is a valid opcode. Using a macro instead of a function
// means that this can be used by the constraint solver.
`define A_OPCODE_IS_VALID(a_opcode) (a_opcode inside {Get, PutFullData, PutPartialData})

// An expression that is true if a_mask is true for every active byte lane. (This is required by the
// PutFullData operation).
//
// Note that the expression actually works by checking there are the right *number* of bits set in
// the mask. The alignment requirement is handled separately.
`define MASK_IS_FULL(a_mask, a_size) ($countones(a_mask) == (1 << a_size))

// The mask must always be LOW for all inactive byte lanes (see TL specification 1.8.1, p26)
//
// To evaluate this, notice that (1 << a_size) gives the number of active byte lanes. Exponentiating
// again gives ((1 << (1 << a_size)) - 1), which is a pattern of bits that are true for the active
// byte lanes, starting at index zero.
//
// Shifting this left by a_addr[SizeWidth-1:0] gives the pattern of bits for the active byte lanes,
// starting at the correct index.
//
// Invert this and then AND with a_mask. Any bits high in the result are inactive byte lanes that
// are HIGH in the mask.
`define MASK_LOW_IN_INACTIVE_LANES(a_mask, a_addr, a_size) \
    ((a_mask & ~(((1 << (1 << a_size)) - 1) << a_addr[SizeWidth-1:0])) == 0)

// Addresses should be naturally aligned. The operation addresses (1 << a_size) bytes, so the
// address should be divisible by that. Equivalently, the bottom a_size bits of a_addr should be
// zero.
`define ADDR_ALIGNED_TO_SIZE(a_addr, a_size) ((a_addr & ((1 << a_size) - 1)) == 0)

// The maximum allowed a_size is 2 (corresponding to a 4-byte / 32-bit operation)
`define BELOW_MAX_A_SIZE(a_size) (a_size <= 2)

class tl_seq_item extends uvm_sequence_item;

  // This block of variables is the fields that are sent on the A side of the transaction
  rand bit [AddrWidth - 1   : 0] a_addr;
  rand bit [DataWidth - 1   : 0] a_data;
  rand bit [MaskWidth - 1   : 0] a_mask;
  rand bit [SizeWidth - 1   : 0] a_size;
  rand bit [2:0]                 a_param;
  rand bit [SourceWidth - 1 : 0] a_source;
  rand bit [OpcodeWidth - 1 : 0] a_opcode;
  rand bit [AUserWidth - 1 : 0]  a_user;

  // This block of variables is the fields that are sent on the D side of the transaction
  rand bit [2:0]                 d_param;
  rand bit [DataWidth - 1   : 0] d_data;
  rand bit [SourceWidth - 1 : 0] d_source;
  rand bit [SizeWidth - 1   : 0] d_size;
  rand bit [OpcodeWidth - 1 : 0] d_opcode;
  rand bit                       d_error;
  rand bit [DUserWidth - 1 : 0]  d_user;
  rand bit                       d_sink;

  // When this item is sent by a host-mode driver, this gives the number of cycles that the driver
  // will wait before asserting a_valid (the VALID signal for a message on the A channel).
  rand int unsigned               a_valid_delay;

  // A TileLink message is sent by asserting the VALID signal and waiting for the receiver to assert
  // READY. On the A channel, the signals are a_valid and a_ready. When the driver is configured to
  // abort early (either by req_abort_after_a_valid_len or cfg.allow_a_valid_drop_wo_a_ready), this
  // variable gives the number of cycles that it will assert a_valid before (if a_ready has been low
  // throughout) aborting the message by dropping a_valid again.
  rand int unsigned               a_valid_len;

  // When this item is sent by a device-mode driver, this gives the number of cycles that the driver
  // will wait before asserting d_valid (the VALID signal for a message on the D channel).
  rand int unsigned               d_valid_delay;

  // A TileLink message is sent by asserting the VALID signal and waiting for the receiver to assert
  // READY. On the D channel, the signals are d_valid and d_ready. When the driver is configured to
  // abort early (either by rsp_abort_after_d_valid_len or cfg.allow_d_valid_drop_wo_d_ready), this
  // variable gives the number of cycles that it will assert d_valid before (if d_ready has been low
  // throughout) aborting the message by dropping d_valid again.
  rand int unsigned               d_valid_len;

  // If this flag is true, a host-mode driver will abort sending a message on the A channel after
  // waiting a_valid_len cycles for a_ready to be asserted by the other end.
  bit                             req_abort_after_a_valid_len;

  // If this flag is true, a host-mode driver will abort sending a message on the D channel after
  // waiting d_valid_len cycles for a_ready to be asserted by the other end.
  bit                             rsp_abort_after_d_valid_len;

  // This signal is filled in by a host-mode driver after it stops sending the item on the A
  // channel. It is set to true if the message was accepted and to false if the request was aborted
  // (either because of timeout or because a reset was asserted).
  bit                             req_completed;

  // This signal is filled in by a device-mode driver after it stops sending the item on the D
  // channel. It is set to true if the message was accepted and to false if the request was aborted
  // (either because of timeout or because a reset was asserted).
  bit                             rsp_completed;

  // The a_param and d_param message fields are reserved in the spec for future use. Force them to
  // be zero in items that we generate.
  extern constraint param_c;

  // Constrain d_error to be false (so the message on the D channel does not report an error). This
  // is a soft constraint, and is overridden in e.g. tl_device_seq, which can inject a nonzero
  // number of error responses.
  extern constraint no_d_error_c;

  // A bound on the time to wait before dropping a_valid if there is no a_ready response.
  extern constraint a_valid_len_c;

  // A bound on the time to wait before dropping d_valid if there is no d_ready response.
  extern constraint d_valid_len_c;

  // A bound on the time to wait before dropping asserting a_valid / d_valid on the A / D channels,
  // respectively.
  extern constraint valid_delay_c;

  // Constrain d_opcode to be a valid one for the D channel.
  extern constraint d_opcode_c;

  // Constrain a_opcode to be a valid one for the A channel.
  extern constraint a_opcode_c;

  // Constrain the mask to be contiguous. Technically, this avoids generating some PutPartialData
  // messages that we should probably allow (e.g. a mask of 4'b1001). As a result, that behaviour
  // won't be tested by randomised testing.
  extern constraint mask_contiguous_c;

  // Require that the mask is high for all active byte lanes for a PutFullData message.
  extern constraint mask_w_PutFullData_c;

  // Require that the mask is only high in active lanes.
  extern constraint mask_in_active_lanes_c;

  // Require that a_addr is naturally aligned for an operation touching (1 << a_size) bytes.
  extern constraint addr_size_align_c;

  // Require that a_size is at most 2 (this constrains messages to be at most 32 bits, so disallows
  // multi-beat messages).
  extern constraint max_size_c;

  `uvm_object_utils_begin(tl_seq_item)
    `uvm_field_int  (a_addr,              UVM_DEFAULT)
    `uvm_field_int  (a_data,              UVM_DEFAULT)
    `uvm_field_int  (a_mask,              UVM_DEFAULT)
    `uvm_field_int  (a_size,              UVM_DEFAULT)
    `uvm_field_int  (a_param,             UVM_DEFAULT)
    `uvm_field_int  (a_source,            UVM_DEFAULT)
    `uvm_field_int  (a_opcode,            UVM_DEFAULT)
    `uvm_field_int  (a_user,              UVM_DEFAULT)
    `uvm_field_int  (d_param,             UVM_DEFAULT)
    `uvm_field_int  (d_source,            UVM_DEFAULT)
    `uvm_field_int  (d_data,              UVM_DEFAULT)
    `uvm_field_int  (d_size,              UVM_DEFAULT)
    `uvm_field_int  (d_opcode,            UVM_DEFAULT)
    `uvm_field_int  (d_error,             UVM_DEFAULT)
    `uvm_field_int  (d_sink,              UVM_DEFAULT)
    `uvm_field_int  (d_user,              UVM_DEFAULT)
    `uvm_field_int  (a_valid_delay,       UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (d_valid_delay,       UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (a_valid_len,         UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (d_valid_len,         UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (req_abort_after_a_valid_len, UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (rsp_abort_after_d_valid_len, UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (req_completed,       UVM_DEFAULT | UVM_NOPACK)
    `uvm_field_int  (rsp_completed,       UVM_DEFAULT | UVM_NOPACK)
  `uvm_object_utils_end

  extern function new (string name = "");
  extern function string convert2string();
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // Set rand_mode(0) for all fields relating to the A channel. This is used when re-randomising an
  // item that has already been populated with data from that channel.
  extern function void disable_a_chan_randomization();

  // The expected value of d_error based on the fields from the A channel item
  extern function bit get_exp_d_error();

  // Return true if a_opcode is not a valid opcode for the A channel.
  extern function bit get_error_a_opcode_invalid();

  // Return the data that is being written by this transaction on the A channel. This is the
  // contents of a_data, but masked by zeroing the bytes where a_mask is false.
  extern function automatic logic [DataWidth-1:0] get_written_data();

  // Return true if the A channel for this item is a PutFullData message and the a_mask field is not
  // high for all the active byte lanes.
  extern function bit get_error_PutFullData_mask_size_mismatched();

  // Return true if the A channel message for this item has an a_addr that is not naturally aligned
  // for the operation size implied by a_size.
  extern function bit get_error_addr_size_misaligned();

  // Return true if the A channel message for this item has bits in a_mask that are high in lanes
  // that are inactive (based on a_addr and a_size).
  extern function bit get_error_mask_not_in_active_lanes();

  // Return true if the A channel message for this item gives an a_size larger than the biggest
  // allowed by OpenTitan tilelink (32 bits, so 4 bytes, so a_size of 2)
  extern function bit get_error_size_over_max();

  // Disable the constraints that apply to the A channel fields. This can be used to generate
  // sequence items that will (almost certainly) cause protocol errors.
  extern function void disable_a_chan_protocol_constraint();

  // Randomise the A channel fields, ensuring that at least one constraint is disabled and the
  // protocol is violated.
  extern function void randomize_a_chan_with_protocol_error();

  // Return true if this sequence item is a write (as opposed to a read).
  extern function bit is_write();

  // Return true if the values in the fields of the D channel message are appropriate as a response
  // to the A channel message.
  extern function bit is_ok();

  // Compute and check the integrity of the a_channel payload.
  //
  // The TL agent is generic and adheres to the TLUL spec, which does not define
  // how the integrity of the payload on each channel is computed / checked. That
  // is up to the chip implementation. Typically, parity / ECC scheme is used, with
  // the redundant bits transmitted through *_user.
  //
  // Returns 1 if the integrity of a_channel is maintained, 0 otherwise. This base
  // class implementation vacuously returns 1.
  extern virtual function bit is_a_chan_intg_ok(bit throw_error = 1'b1);

  // d_channel version of the function above
  extern virtual function bit is_d_chan_intg_ok(bit en_rsp_intg_chk = 1,
                                                bit en_data_intg_chk = 1,
                                                bit throw_error = 1'b1);
endclass

constraint tl_seq_item::param_c {
  a_param == 0;
  d_param == 0;
}

constraint tl_seq_item::no_d_error_c {
  soft d_error == 0;
}

constraint tl_seq_item::a_valid_len_c {
  a_valid_len inside {[1:10]};
}

constraint tl_seq_item::d_valid_len_c {
  d_valid_len inside {[1:10]};
}

constraint tl_seq_item::valid_delay_c {
  a_valid_delay inside {[0:50]};
  d_valid_delay inside {[0:50]};
}

constraint tl_seq_item::d_opcode_c {
  d_opcode inside {AccessAckData, AccessAck};
}

constraint tl_seq_item::a_opcode_c {
  `A_OPCODE_IS_VALID(a_opcode);
}

constraint tl_seq_item::mask_contiguous_c {
  $countones(a_mask ^ {a_mask[MaskWidth-2:0], 1'b0}) <= 2;
}

constraint tl_seq_item::mask_w_PutFullData_c {
  a_opcode == PutFullData -> `MASK_IS_FULL(a_mask, a_size);
}

constraint tl_seq_item::mask_in_active_lanes_c {
  `MASK_LOW_IN_INACTIVE_LANES(a_mask, a_addr, a_size);
}

constraint tl_seq_item::addr_size_align_c {
  `ADDR_ALIGNED_TO_SIZE(a_addr, a_size);
}

constraint tl_seq_item::max_size_c {
  `BELOW_MAX_A_SIZE(a_size);
}

function tl_seq_item::new (string name = "");
  super.new(name);
endfunction

function string tl_seq_item::convert2string();
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
         $sformatf("a_user = 0x%0h ", a_user),
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

function void tl_seq_item::disable_a_chan_randomization();
  a_addr.rand_mode(0);
  a_data.rand_mode(0);
  a_mask.rand_mode(0);
  a_size.rand_mode(0);
  a_param.rand_mode(0);
  a_source.rand_mode(0);
  a_opcode.rand_mode(0);
endfunction

function bit tl_seq_item::get_exp_d_error();
  return get_error_a_opcode_invalid() || get_error_PutFullData_mask_size_mismatched() ||
         get_error_addr_size_misaligned() ||
         get_error_mask_not_in_active_lanes() || get_error_size_over_max();
endfunction

function bit tl_seq_item::get_error_a_opcode_invalid();
  return !`A_OPCODE_IS_VALID(a_opcode);
endfunction

function automatic logic [DataWidth-1:0] tl_seq_item::get_written_data();
  logic [DataWidth-1:0] masked_data = 'x;
  `DV_CHECK(is_write(), "get_written_data() may only be called on a write")
  for (int i = 0; i < MaskWidth; i++) begin
    if (a_mask[i] == 1'b1) begin
      masked_data[8*i +: 8] = a_data[8*i +: 8];
    end
  end
  return masked_data;
endfunction

function bit tl_seq_item::get_error_PutFullData_mask_size_mismatched();
  return (a_opcode == PutFullData) && !(`MASK_IS_FULL(a_mask, a_size));
endfunction

function bit tl_seq_item::get_error_addr_size_misaligned();
  return !(`ADDR_ALIGNED_TO_SIZE(a_addr, a_size));
endfunction

function bit tl_seq_item::get_error_mask_not_in_active_lanes();
  return !`MASK_LOW_IN_INACTIVE_LANES(a_mask, a_addr, a_size);
endfunction

function bit tl_seq_item::get_error_size_over_max();
  return !`BELOW_MAX_A_SIZE(a_size);
endfunction // get_error_size_over_max

// Note: the do_compare() method should only be coded for those properties which can be compared
// that's the reason why the following fields are not part it:
// req_abort_after_a_valid_len, rsp_abort_after_d_valid_len, req_completed, rsp_completed
function bit tl_seq_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  tl_seq_item rhs_;
  // If the cast fails, comparison has also failed
  // A check for null is not needed because that is done in the compare() function which
  // calls do_compare()
  if (!$cast(rhs_, rhs)) begin
    return 0;
  end

  return (super.do_compare(rhs, comparer)                                    &&
          (a_addr                      == rhs_.a_addr                      ) &&
          (a_data                      == rhs_.a_data                      ) &&
          (a_mask                      == rhs_.a_mask                      ) &&
          (a_size                      == rhs_.a_size                      ) &&
          (a_param                     == rhs_.a_param                     ) &&
          (a_source                    == rhs_.a_source                    ) &&
          (a_opcode                    == rhs_.a_opcode                    ) &&
          (a_user                      == rhs_.a_user                      ) &&
          (d_data                      == rhs_.d_data                      ) &&
          (d_size                      == rhs_.d_size                      ) &&
          (d_param                     == rhs_.d_param                     ) &&
          (d_source                    == rhs_.d_source                    ) &&
          (d_opcode                    == rhs_.d_opcode                    ) &&
          (d_error                     == rhs_.d_error                     ) &&
          (d_user                      == rhs_.d_user                      ) &&
          (d_sink                      == rhs_.d_sink                      ));
endfunction

function void tl_seq_item::disable_a_chan_protocol_constraint();
  a_opcode_c.constraint_mode(0);
  mask_contiguous_c.constraint_mode(0);
  mask_w_PutFullData_c.constraint_mode(0);
  mask_in_active_lanes_c.constraint_mode(0);
  addr_size_align_c.constraint_mode(0);
  max_size_c.constraint_mode(0);
endfunction

function void tl_seq_item::randomize_a_chan_with_protocol_error();
  bit cm_a_opcode, cm_mask_w_PutFullData;
  bit cm_mask_in_active_lanes, cm_addr_size_align, cm_max_size;

  // Randomly pick some constraint mode (enabled or disabled) for the various constraints, disabling
  // at least one of them.
  `DV_CHECK_FATAL(std::randomize(cm_a_opcode, cm_mask_w_PutFullData,
                                 cm_mask_in_active_lanes, cm_addr_size_align, cm_max_size) with {
                                   !(&{cm_a_opcode, cm_mask_w_PutFullData,
                                       cm_mask_in_active_lanes, cm_addr_size_align && cm_max_size});
                                 })

  // Apply the selected modes to the constraints that might be disabled
  a_opcode_c.constraint_mode(cm_a_opcode);
  mask_w_PutFullData_c.constraint_mode(cm_mask_w_PutFullData);
  mask_in_active_lanes_c.constraint_mode(cm_mask_in_active_lanes);
  addr_size_align_c.constraint_mode(cm_addr_size_align);
  max_size_c.constraint_mode(cm_max_size);

  // Now randomise this object, ensuring that at least constraint we just disabled is actually being
  // violated.
  `DV_CHECK_FATAL(randomize() with {
                    (!cm_a_opcode && !`A_OPCODE_IS_VALID(a_opcode)) ||
                    (!cm_mask_w_PutFullData &&
                     (a_opcode == PutFullData) && !(`MASK_IS_FULL(a_mask, a_size))) ||
                    (!cm_mask_in_active_lanes &&
                     !(`MASK_LOW_IN_INACTIVE_LANES(a_mask, a_addr, a_size))) ||
                    (!cm_addr_size_align && !`ADDR_ALIGNED_TO_SIZE(a_addr, a_size)) ||
                    (!cm_max_size && !`BELOW_MAX_A_SIZE(a_size));
                  })
endfunction

function bit tl_seq_item::is_write();
  return (a_opcode inside {PutFullData, PutPartialData});
endfunction

function bit tl_seq_item::is_ok();
  // For this to be an appropriate response, the D channel has to hold something that could be a
  // response to the request on the A channel. For a Get, TileLink expects an AccessAckData; for a
  // write or error opcode, it expects AccessAck
  tl_d_op_e exp_d_opcode = (a_opcode == Get) ? tlul_pkg::AccessAckData : tlul_pkg::AccessAck;
  return (d_opcode == exp_d_opcode) && (a_source == d_source);
endfunction

function bit tl_seq_item::is_a_chan_intg_ok(bit throw_error = 1'b1);
  return 1;
endfunction

function bit tl_seq_item::is_d_chan_intg_ok(bit en_rsp_intg_chk = 1,
                                            bit en_data_intg_chk = 1,
                                            bit throw_error = 1'b1);
  return 1;
endfunction

`undef BELOW_MAX_A_SIZE
`undef ADDR_ALIGNED_TO_SIZE
`undef MASK_LOW_IN_INACTIVE_LANES
`undef MASK_IS_FULL
`undef A_OPCODE_IS_VALID
