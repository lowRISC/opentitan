// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

typedef class tl_host_base_seq;

// A register adapter parameterized with the default tl_seq_item type. The idea is to extend
// tl_seq_item for further constraints or customizations if required and create the tl_reg_adapter
// instance with the overridden type.

class tl_reg_adapter #(type ITEM_T = tl_seq_item) extends uvm_reg_adapter;
  `uvm_object_param_utils(tl_reg_adapter#(ITEM_T))

  // Ensure that when an instance of this adapter is created, the cfg handle below is initialized to
  // the `tl_agent_cfg` instance associated with this adapter instance.
  tl_agent_cfg cfg;

  // Information about how to represent RACL role and uid values in the TL item. This has to be
  // configured from the test environment (which can see the dut) because it depends on the
  // top-level that is being modelled.
  //
  // The default is not to support either (so role and uid are both signalled as zero)
  local int unsigned role_lsb, role_nbits;
  local int unsigned uid_lsb, uid_nbits;

  extern function new(string name = "");

  // Standard uvm_reg_adapter functions
  extern function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
  extern function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);

  // Configure and randomise a bus request for a register read or write
  extern local function void fill_bus_rd(const ref uvm_reg_bus_op rw, ref ITEM_T bus_req);
  extern local function void fill_bus_wr(const ref uvm_reg_bus_op rw, ref ITEM_T bus_req);

  // Return the highest bit index in the target of a uvm_reg_item. This will be the highest bit in a
  // field of a register, or will be the bus width if item is a memory.
  extern local function int unsigned get_tgt_msb(uvm_reg_item item);

  // Check that the requested bit indices for something will fit in the A channel's user field.
  extern local function bit check_user_bit_idx(string       field_name,
                                               int unsigned lsb,
                                               int unsigned nbits);

  // Configure how to represent RACL roles and uids
  extern function void configure_racl_bits(int unsigned role_lsb,
                                           int unsigned role_nbits,
                                           int unsigned uid_lsb,
                                           int unsigned uid_nbits);
endclass

function tl_reg_adapter::new(string name = "");
  super.new(name);
  // Force the uvm_reg_map to use this sequence to sync with the driver instead.
  parent_sequence = tl_host_base_seq#(ITEM_T)::type_id::create("parent_sequence");
  supports_byte_enable = 1;
  provides_responses = 1;
endfunction

function uvm_sequence_item tl_reg_adapter::reg2bus(const ref uvm_reg_bus_op rw);
  ITEM_T bus_req = ITEM_T::type_id::create("bus_req");

  if (rw.kind == UVM_READ) begin
    fill_bus_rd (rw, bus_req);
  end else begin
    fill_bus_wr (rw, bus_req);
  end

  if (cfg.csr_access_abort_pct_in_adapter > $urandom_range(0, 100)) begin
    bus_req.req_abort_after_a_valid_len = 1;
    `uvm_info(`gfn, $sformatf("tl reg req item is allowed to be aborted"), UVM_MEDIUM)
  end
  `uvm_info(`gfn, {"tl_reg_adapter::reg2bus: ", bus_req.convert2string()}, UVM_HIGH)
  return bus_req;
endfunction

function void tl_reg_adapter::bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
  ITEM_T bus_rsp;
  `downcast(bus_rsp, bus_item)
  rw.kind    = bus_rsp.is_write() ? UVM_WRITE : UVM_READ;
  rw.addr    = bus_rsp.a_addr;
  rw.data    = (rw.kind == UVM_WRITE) ? bus_rsp.a_data : bus_rsp.d_data;
  rw.byte_en = bus_rsp.a_mask;
  `DV_CHECK_EQ(bus_rsp.d_source, bus_rsp.a_source)
  // indicate if the item is completed successfully for upper level to update predict value
  rw.status  = !bus_rsp.req_completed ? UVM_NOT_OK : UVM_IS_OK;
  `uvm_info(`gfn, {"tl_reg_adapter::bus2reg: ", bus_rsp.convert2string()}, UVM_HIGH)
endfunction

function void tl_reg_adapter::fill_bus_rd(const ref uvm_reg_bus_op rw, ref ITEM_T bus_req);
  // The tl_seq_item::mask_in_active_lanes_c constraint ensures that a_mask is only asserted in
  // active byte lanes. For 50% of CSR full reads (with element_kind == UVM_REG and all bits set in
  // byte_en), we ask mask to be asserted for a strict subset of the lanes.
  bit is_csr_full_read = (rw.byte_en == '1 && get_item().element_kind == UVM_REG);

  if (!bus_req.randomize() with {
        bus_req.a_opcode == tlul_pkg::Get;
        bus_req.a_addr[AddrWidth-1:2] == local::rw.addr[AddrWidth-1:2];
        if (local::is_csr_full_read) {
          $countones(bus_req.a_mask) dist {MaskWidth :/ 1, [0:MaskWidth-1] :/ 1};
        } else {
          bus_req.a_mask == rw.byte_en[MaskWidth-1:0];
        }
      }) begin
    `uvm_fatal(get_name(), "Failed to randomize bus request for read")
  end
endfunction

function void tl_reg_adapter::fill_bus_wr(const ref uvm_reg_bus_op rw, ref ITEM_T bus_req);
  // The TL bus may support byte-enable values, which might be given by allowing some bits of a_mask
  // to be zero. Since CSRs in OpenTitan don't support partial accesses, the reg adapter wants to
  // choose an a_mask which is true for every byte that exists in the target.
  //
  // The tl_seq_item::mask_contiguous_c constraint means that we can require that the bytes
  // containing bits 0..msb are enabled by just requiring the ends to be enabled. These are the
  // bytes with indices 0 and msb / 8.
  int unsigned msb = supports_byte_enable ? get_tgt_msb(get_item()) : (DataWidth - 1);

  if (!bus_req.randomize() with {
        bus_req.a_opcode inside {PutFullData, PutPartialData};
        bus_req.a_addr        == AddrWidth'(rw.addr);
        bus_req.a_data        == DataWidth'(rw.data);
        bus_req.a_mask[0]     == 1;
        bus_req.a_mask[msb/8] == 1;
      }) begin
    `uvm_fatal(get_name(), "Failed to randomize bus request for write")
  end
endfunction

function int unsigned tl_reg_adapter::get_tgt_msb(uvm_reg_item item);
  case (item.element_kind)
    UVM_REG: begin
      // We only support registers that are instances of dv_base_reg. These registers have an msb
      // position pre-calculated, which gives the highest bit that is contained in any field.
      dv_base_reg csr;
      if (!$cast(csr, item.element)) begin
        `uvm_fatal(get_name(), "Cannot cast UVM_REG item to a dv_base_reg.")
      end
      return csr.get_msb_pos();
    end

    UVM_FIELD: begin
      uvm_reg_field field;
      if (!$cast(field, item.element)) begin
        `uvm_fatal(get_name(), "Cannot cast UVM_FIELD item to a uvm_reg_field.")
      end
      return field.get_lsb_pos() + field.get_n_bits() - 1;
    end

    UVM_MEM: begin
      // Set msb to be the top bit of a_data, forcing all of the a_mask bits to be set.
      return DataWidth - 1;
    end

    default:
      `uvm_fatal(get_name(), $sformatf("Unknown element_kind: %0p", item.element_kind))
  endcase
endfunction

function bit tl_reg_adapter::check_user_bit_idx(string       field_name,
                                                int unsigned lsb,
                                                int unsigned nbits);
  if (nbits > 0 && lsb + nbits >= AUserWidth) begin
    `uvm_error(this.get_name(),
               $sformatf("Cannot represent RACL %s with lsb %0d and %0d bits: AUserWidth is %0d",
                         field_name, lsb, nbits, AUserWidth))
    return 0;
  end
  return 1;
endfunction

function void tl_reg_adapter::configure_racl_bits(int unsigned role_lsb,
                                                  int unsigned role_nbits,
                                                  int unsigned uid_lsb,
                                                  int unsigned uid_nbits);
  // Check that both sides can fit in the USER field for the A channel, zeroing out their width if
  // not. If either doesn't fit, its call to check_user_bit_idx will have reported a uvm_error.
  if (!check_user_bit_idx("role", role_lsb, role_nbits)) role_nbits = 0;
  if (!check_user_bit_idx("uid", uid_lsb, uid_nbits)) uid_nbits = 0;

  this.role_lsb = role_lsb;
  this.role_nbits = role_nbits;
  this.uid_lsb = uid_lsb;
  this.uid_nbits = uid_nbits;
endfunction
