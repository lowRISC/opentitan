// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Configuration class for TileLink agent
// ---------------------------------------------
class tl_agent_cfg extends dv_base_agent_cfg;

  virtual tl_if  vif;
  // TileLink conformance level supported by this agent
  // Right now only TL-UL is supported
  tl_level_e tl_level = kTLUL;

  // Maximum number of outstanding transactions supported by the DUT.
  // 0: Unlimited from the host perspective, might be back-pressured by the device
  // 1: Only single transaction at a time
  // n: Number of maximum oustanding requests

  // This is initialized to an arbitrary value. The DUT may actually support higher or lower than
  // this number. Calculating exactly how many outstanding transactions the DUT supports is hard to
  // determine. For most comportable IPs, it will likely be less than 16. The testbench attempts to
  // pump the DUT with as many transactions as possible. The missing coverage in
  // `tl_agent_cov::max_outstanding_cfg` will then indicate what the design actually supported.
  // The designer must then confirm if that looks correct (in the coverage report), and then this
  // value is updated accordingly in the DUT's test / env class.
  //
  // Note that this is a device constant. It should only be set within the scope of the test class'
  // build_phase. Once set, it MUST NOT BE modified whatsoever.
  int unsigned max_outstanding_req = 16;

  // If allow_a_valid_drop_wo_a_ready then the host can de-assert valid if there is no response from
  // the device on the A channel. The other knobs control how this works. Each transaction has a
  // "valid_len". If the host hasn't seen a ready after holding valid high for that many cycles, it
  // will de-assert valid for a time before retrying.
  //
  // If use_seq_item_a_valid_len is true then valid_len will be read from the sequence item (field
  // a_valid_len). If not, it will be picked uniformly between a_valid_len_min and a_valid_len_max.
  bit allow_a_valid_drop_wo_a_ready = 1;
  bit use_seq_item_a_valid_len;
  int unsigned a_valid_len_min = 1;
  int unsigned a_valid_len_max = 10;

  // Knobs controlling when we de-assert valid in device mode: see above for the host mode
  // equivalent.
  bit use_seq_item_d_valid_len;
  bit allow_d_valid_drop_wo_d_ready;
  int unsigned d_valid_len_min = 1;
  int unsigned d_valid_len_max = 10;

  // TileLink channel valid delay (host mode)
  bit use_seq_item_a_valid_delay;
  int unsigned a_valid_delay_min = 0;
  int unsigned a_valid_delay_max = 10;

  // TileLink channel ready delay (host mode)
  int unsigned d_ready_delay_min = 0;
  int unsigned d_ready_delay_max = 10;

  // TileLink channel ready delay (device mode)
  int unsigned a_ready_delay_min = 0;
  int unsigned a_ready_delay_max = 10;

  // TileLink channel ready delay (device mode)
  bit use_seq_item_d_valid_delay;
  int unsigned d_valid_delay_min = 0;
  int unsigned d_valid_delay_max = 10;

  // TL spec requires host to set d_ready = 1 when a_valid = 1, but some design may not follow this
  // rule. Details at #3208. Use below knob to control
  bit host_can_stall_rsp_when_a_valid_high = 0;

  // knob for device to enable/disable same cycle response
  bit device_can_rsp_on_same_cycle = 0;

  // A configuration flag for the monitor that configures whether it should synchronise concurrent A
  // and D transactions or not. See note above the definition of channel_dir_port in tl_monitor.sv
  // for details.
  bit synchronise_ports = 1'b0;

  // for same cycle response, need to know when a_valid and other data/control are available, so
  // that monitor can sample it, then send to sequence to get data for response in the same cycle
  // 10 means 10% of TL clock period. This var is only use when device_can_rsp_on_same_cycle = 1
  time time_a_valid_avail_after_sample_edge = 1ns;

  // Sets the valid a_source width. The DUT may support fewer bits than the whole SourceWidth bits.
  int unsigned valid_a_source_width = SourceWidth;

  // Maintains a queue of a_source values used in previous TL requests.
  //
  // The queue size maxes out at max_outstanding_req value, beyond which the a_source values can
  // be recycled. The a_source value for a new request is randomized such that it does not match any
  // in this queue. The new a_source is pushed into the back of the queue and the oldest one is
  // popped from the front when the max size is reached.
  //
  // NOTE: If a tl_seq_item is being constructed for a new host request (whether in the TL
  // sequences, adapter or elsewhere), it is mandatory to constrain the tl_seq_item::a_source to NOT
  // match what already exists in the queue. Otherwise, it will violate the spec and the design will
  // end up throwing assertion errors. It is recommended to use the `randomize_a_source_in_req()`
  // function below to achieve this.
  bit [SourceWidth-1:0] a_source_pend_q[$];

  // Records the a_source value that was last released from the `a_source_pend_q` pool.
  // We influence the randomization of a new req's a_source to reuse this 20% (also a knob) of the
  // time. The initial value is randomized (see post_randomize()).
  protected bit [SourceWidth-1:0] last_a_source_released;

  // Sets the randomization dist weight for a new a_source value to be constrained to the last
  // a_source released. This only ATTEMPTS to set the a_source to the last_a_source_released value -
  // it is not always guaranteed even at 100%, especially if the test does non-blocking accessses.
  rand int unsigned use_last_a_source_released_pct = 20;

  // The monitor detects reset and maintains the value below.
  bit reset_asserted;

  constraint a_source_eq_last_a_source_released_pct_c {
    use_last_a_source_released_pct <= 100;
    use_last_a_source_released_pct dist {
      [0:19]  :/ 1,
      [20:59] :/ 1,
      [60:99] :/ 1,
      100     :/ 1
    };
  }

  // TLUL allows host to switch content if the item isn't accepted. RAL doesn't provide interface
  // to control this. Use this knob to allow tl_reg_adapter to randomize req_abort_after_a_valid_len
  // Note: below set the chance to abort after a_valid_len in tl_reg_adapter. if > 0, csr access may
  // return UVM_NOT_OK when the item is aborted without accepted.
  int unsigned csr_access_abort_pct_in_adapter = 0;

  // Indicate whether to check TLUL errors.
  // Added to allow some TLUL checks to be ignored on certain scenarios.
  bit check_tl_errs = 1'b1;

  // Invalidate drive option
  // Setting these to '1', make driver send 'x' during invalidate cycle.
  // Setting these to '0', make driver send 'random value' during invalidate cycle.
  rand bit invalidate_a_x;
  rand bit invalidate_d_x;

  constraint invalidate_a_channel_op_c {
    invalidate_a_x dist { 1 := 7, 0 := 3};
  }
  constraint invalidate_d_channel_op_c {
    invalidate_d_x dist { 1 := 7, 0 := 3};
  }


  `uvm_object_utils_begin(tl_agent_cfg)
    `uvm_field_int(max_outstanding_req,   UVM_DEFAULT)
    `uvm_field_enum(tl_level_e, tl_level, UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(a_ready_delay_max,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_min,     UVM_DEFAULT)
    `uvm_field_int(d_ready_delay_max,     UVM_DEFAULT)
    `uvm_field_int(host_can_stall_rsp_when_a_valid_high, UVM_DEFAULT)
    `uvm_field_int(device_can_rsp_on_same_cycle,         UVM_DEFAULT)
    `uvm_field_int(time_a_valid_avail_after_sample_edge, UVM_DEFAULT)
    `uvm_field_int(csr_access_abort_pct_in_adapter,      UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  function void post_randomize();
    // We want to randomize the initial value of last_a_source_released, while respecting any
    // constraints on a_source in the tl_seq_item (and its extensions). So we do it here instead.
    tl_seq_item dummy = tl_seq_item::type_id::create("dummy");
    `DV_CHECK_RANDOMIZE_FATAL(dummy)
    randomize_a_source_in_item(.item(dummy), .use_last_a_source_released(1'b0));
    last_a_source_released = dummy.a_source;
  endfunction

  // Randomizes a_source within an item (protected function).
  //
  // This function takes the tl_seq_item object to specifically randomize the a_source such that it
  // does not match an existing one in the a_source_q. This randomization also takes into account
  // any existing constriants on a_source that may exist in the class definition. The new a_source
  // value is randomized to be equal to the last a_source released from the a_source_pend_q
  // 20% of the time (weight is configurable).
  //
  // For actual reqs made out to the DUT, use randomize_a_source_in_req().
  protected function void randomize_a_source_in_item(tl_seq_item item,
                                                     bit use_last_a_source_released);
    bit [SourceWidth - 1 : 0] a_source;

    // Use std::randomize instead of calling item.randomize(a_source). item.randomize will invoke
    // post_randomize. If user does sth after post_randomize before calling finish_item, invoking
    // post_randomize may override that.
    // For example, if we use item.randomize(a_source)
    // item.randomize(); // in post_randomize, instr_type is set to False
    // item.instr_type = True;
    // finish_item(item); // finish_item will call randomize_a_source_in_item.
    //                    // item.randomize(a_source) will invoke post_randomize, instr_type is set
    //                    // to False again.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(a_source,
        // use soft constraint as seq may still send req when all the valid a_source are used
        (!reset_asserted) -> soft !(a_source inside {a_source_pend_q});
        // Set the upper a_source bits that are unused to 0.
        (a_source >> valid_a_source_width) == 0;
        // We cannot guarantee that last_a_source_released is not in a_source_pend_q,
        // especially if the test does non-blocking accesses. If the a_source for the new req
        // needs to be equal to last_a_source_released, we will need the bottom constraint to be a
        // soft one to *potentially* avoid violating the previous constraint. Only way to guarantee
        // that the new a_source == last_a_source_released is to ensure the test only does blocking
        // accesses.
        use_last_a_source_released && !(last_a_source_released inside {a_source_pend_q})
            -> soft (a_source == last_a_source_released);)
    item.a_source = a_source;
    `uvm_info(`gfn, $sformatf("a_source_pend_q: %p a_source: %0h", a_source_pend_q, item.a_source), UVM_DEBUG)
  endfunction

  // Randomizes the a_source for a 'real' req (public version of the above function).
  //
  // Invokes randomize_a_source_in_item() and adds the a_source for the new req to the queue.
  virtual function void randomize_a_source_in_req(tl_seq_item item);
    bit use_last_a_source_released;
    use_last_a_source_released = ($urandom_range(1, 100) <= use_last_a_source_released_pct);
    randomize_a_source_in_item(item, use_last_a_source_released);
    add_to_a_source_pend_q(item.a_source);
  endfunction

  // Adds a_source to the a_source_pend_q.
  //
  // Ensures that the queue does not exceed the max outstanding req size. Pops the oldest a_source
  // used to last_a_source_released.
  virtual function void add_to_a_source_pend_q(bit [SourceWidth-1:0] a_source);
    if (reset_asserted) return;
    if (a_source_pend_q.size() == max_outstanding_req) begin
      last_a_source_released = a_source_pend_q.pop_front();
    end
    a_source_pend_q.push_back(a_source);
    `uvm_info(`gfn, $sformatf("a_source_pend_q: %p", a_source_pend_q), UVM_DEBUG)
  endfunction

  // Removes the last used a_source from a_source_pend_q.
  //
  // Invoked by the tl_host_base_seq::get_base_response() which overrides the default UVM
  // implementation. It is recommended that all TL host sequence flavors that do not extended from
  // tl_host_base_seq invoke this function similarly to avoid running out of a_source IDs when
  // creating non-blocking requests.
  virtual function void remove_from_a_source_pend_q(bit [SourceWidth-1:0] a_source);
    int result[$];

    // Responses can return out of order, so the a_source can be anywhere in the queue.
    result = a_source_pend_q.find_first_index with (item == a_source);
    if (result.size() == 1) begin
      a_source_pend_q.delete(result.pop_front());
      last_a_source_released = a_source;
      `uvm_info(`gfn, $sformatf("a_source_pend_q: %p", a_source_pend_q), UVM_DEBUG)
    end
  endfunction

endclass
