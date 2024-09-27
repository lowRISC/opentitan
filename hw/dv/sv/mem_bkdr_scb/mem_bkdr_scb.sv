// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

virtual class mem_bkdr_scb #(int AddrWidth = bus_params_pkg::BUS_AW,
                             int DataWidth = bus_params_pkg::BUS_DW) extends uvm_object;

  localparam int MaskWidth  = DataWidth / 8;

  typedef bit [AddrWidth-1:0] mem_addr_t;
  typedef bit [DataWidth-1:0] mem_data_t;
  typedef bit [MaskWidth-1:0] mem_mask_t;

  typedef struct {
    mem_addr_t addr;
    mem_data_t data;
    mem_mask_t mask;
  } mem_item_t;

  // Queue to save pending items
  mem_item_t read_item_q[$];
  mem_item_t write_item_q[$];

  bit en_cov;

  // covers that all combinations of reads/writes can create b2b scenario
  covergroup b2b_access_types_cg(string name) with function sample(bit addr_collision,
                                                                   bit first_write_en,
                                                                   bit second_write_en,
                                                                   bit first_partial_acc,
                                                                   bit second_partial_acc);
    option.per_instance = 1;
    option.name         = name;
    raw_hazard_cp: coverpoint addr_collision;
    b2b_access_types_cp: coverpoint {first_write_en, second_write_en};
    b2b_partial_types_cp: coverpoint {first_partial_acc, second_partial_acc};

    all_cross: cross raw_hazard_cp, b2b_access_types_cp, b2b_partial_types_cp;
  endgroup

  function new (string name = "");
    super.new(name);
    b2b_access_types_cg = new(name);
  endfunction : new

  // User must override this function to return backdoor value from the memory based on given addr
  pure virtual function mem_data_t get_bkdr_val(mem_addr_t addr);

  function void reset();
    read_item_q.delete();
    write_item_q.delete();
  endfunction

  // utility function to expand a TLUL mask to a full bit-mask
  function mem_data_t expand_bit_mask(mem_mask_t mask);
    mem_data_t bitmask = '0;
    for (int i = 0; i < MaskWidth; i++) begin
      bitmask[i*8 +: 8] = {8{mask[i]}};
    end
    return bitmask;
  endfunction

  // Check if read-after-write hazard occurs. If so, return 1 and output data & mask of the last
  // match item
  function bit check_raw_hazard(input mem_addr_t addr,
                                output mem_data_t data, output mem_mask_t mask);
    int found_idx_q[$];

    found_idx_q = write_item_q.find_last_index() with (item.addr == addr);
    if (found_idx_q.size) begin
      data = write_item_q[found_idx_q[0]].data;
      mask = write_item_q[found_idx_q[0]].mask;
      return 1;
    end else begin
      return 0;
    end
  endfunction

  // check the item is consistent between read|write_start and read|write_finish
  function void check_item_consistency(mem_item_t start_item,
                                       mem_addr_t finish_item_addr,
                                       mem_mask_t finish_item_mask);
    `DV_CHECK_EQ(start_item.addr, finish_item_addr)
    `DV_CHECK_EQ(start_item.mask, finish_item_mask)
  endfunction

  // Call this function when a read request is latched by design
  // Predicted read value is calculated in this function:
  //  - If there is a pending write with same addr (RAW hazard), the expected value is from this
  //  write (also depends on which bytes is enabled)
  //  - If no RAW hazard, the expected value is from latching backdoor value at the time of calling
  //  this function
  function void read_start(mem_addr_t addr, mem_mask_t mask);
    bit is_raw;
    mem_data_t raw_data, bkdr_data, exp_data;
    mem_mask_t raw_mask;
    mem_data_t raw_bit_mask, exp_bit_mask;

    is_raw = check_raw_hazard(addr, raw_data, raw_mask);
    if (is_raw) begin
      raw_bit_mask = expand_bit_mask(raw_mask);
      `uvm_info(`gfn, $sformatf("Found RAW hazard : Addr[0x%0h], Data[0x%0h], Mask[0x%0h]",
                                addr, raw_data, raw_mask), UVM_MEDIUM)
    end

    bkdr_data = get_bkdr_val(addr);
    exp_data = (raw_data & raw_bit_mask) | (bkdr_data & ~raw_bit_mask);

    exp_bit_mask = expand_bit_mask(mask);
    exp_data &= exp_bit_mask;

    read_item_q.push_back(mem_item_t'{addr, exp_data, mask});

    `uvm_info(`gfn, $sformatf("read_start : Addr[0x%0h], Exp_data[0x%0h], Mask[0x%0h]",
                              addr, exp_data, mask), UVM_MEDIUM)
  endfunction

  // Call this function when a read transaction is done and compare the read value with expected
  // value calculated at read_start
  function void read_finish(mem_data_t act_data,
                            mem_addr_t addr = 0,
                            mem_mask_t mask = '1,
                            bit en_check_consistency = 1,
                            bit en_check_exp = 1);
    mem_item_t exp_item;
    `DV_CHECK_NE(read_item_q.size, 0)
    exp_item = read_item_q.pop_front();
    act_data &= expand_bit_mask(mask);

    if (en_check_consistency) check_item_consistency(exp_item, addr, mask);

    if (en_check_exp) begin
      `DV_CHECK_EQ(act_data, exp_item.data,
                   $sformatf("addr 0x%0h read out mismatch", exp_item.addr))
    end

    `uvm_info(`gfn, $sformatf("read_finish: Addr[0x%0h], data[0x%0h], Mask[0x%0h]",
                              exp_item.addr, act_data, exp_item.mask), UVM_MEDIUM)

    sample_b2b_cg(.write(0), .addr(addr), .mask(mask));
  endfunction

  // Call this function when a write request is latched by design
  // Write item will be stored in the queue for checking RAW hazard and future comparison
  function void write_start(mem_addr_t addr, mem_data_t exp_data, mem_mask_t mask);
    write_item_q.push_back(mem_item_t'{addr, exp_data, mask});
    `uvm_info(`gfn, $sformatf("write_start : Addr[0x%0h], Exp_data[0x%0h], Mask[0x%0h]",
                              addr, exp_data, mask), UVM_MEDIUM)
  endfunction

  // Call this function once the write data is written into the memory
  // this function will read back the data from backdoor and compare with write value stored in
  // write_item_q
  function void write_finish(mem_addr_t addr = 0,
                             mem_mask_t mask = '1,
                             bit en_check_consistency = 1,
                             bit en_check_exp = 1);
    mem_data_t act_data, exp_data;
    mem_data_t bit_mask;
    mem_item_t exp_item;
    `DV_CHECK_NE(write_item_q.size, 0)
    exp_item = write_item_q.pop_front();
    bit_mask = expand_bit_mask(exp_item.mask);

    if (en_check_consistency) check_item_consistency(exp_item, addr, mask);

    act_data = get_bkdr_val(exp_item.addr) & bit_mask;
    exp_data = exp_item.data & bit_mask;

    if (en_check_exp) begin
      `DV_CHECK_EQ(act_data, exp_data,
                   $sformatf("addr 0x%0h write mismatch", exp_item.addr))
    end

    `uvm_info(`gfn, $sformatf("write_finish: Addr[0x%0h], data[0x%0h], Mask[0x%0h]",
                              exp_item.addr, act_data, exp_item.mask), UVM_MEDIUM)

    sample_b2b_cg(.write(1), .addr(addr), .mask(mask));
  endfunction

  function void sample_b2b_cg(bit write, mem_addr_t addr, mem_mask_t mask);
    if (en_cov && (write_item_q.size + read_item_q.size == 1)) begin
      mem_item_t second_item;
      bit second_write_en;

      if (write_item_q.size) begin
        second_item     = write_item_q[0];
        second_write_en = 1;
      end else begin
        second_item     = read_item_q[0];
        second_write_en = 0;
      end
      b2b_access_types_cg.sample(.addr_collision(second_item.addr == addr),
                                 .first_write_en(write),
                                 .second_write_en(second_write_en),
                                 .first_partial_acc(mask != '1),
                                 .second_partial_acc(second_item.mask != '1));
    end
  endfunction
endclass
