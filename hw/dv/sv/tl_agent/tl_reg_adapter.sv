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
  uvm_reg_item item = get_item();
  ITEM_T bus_req;
  bus_req = ITEM_T::type_id::create("bus_req");

  // randomize CSR partial or full read for partial read DUT (except memory) always return the
  // entire 4 bytes bus data if CSR full read (all bytes are enabled) & !MEM, randomly select full
  // or partial read if CSR field read, will do a partial read if protocal allows by setting a_mask
  // to byte_en
  if (rw.kind == UVM_READ) begin
    if (rw.byte_en == '1 && item.element_kind == UVM_REG) begin // csr full read
      `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_req,
          a_opcode              == tlul_pkg::Get;
          a_addr[AddrWidth-1:2] == rw.addr[AddrWidth-1:2];
          $countones(a_mask)  dist {MaskWidth       :/ 1,
                                    [0:MaskWidth-1] :/ 1};)
    end else begin // csr field read
      `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_req,
          a_opcode              == tlul_pkg::Get;
          a_addr[AddrWidth-1:2] == rw.addr[AddrWidth-1:2];
          a_mask                == rw.byte_en[MaskWidth-1:0];)
    end
  end else begin // randomize CSR partial or full write
    // Actual width of the CSR may be < DataWidth bits depending on fields and their widths. In that
    // case, the transaction size in bytes and partial write mask need to be at least as wide as the
    // CSR to be a valid transaction. Otherwise, the DUT can return an error response.
    int msb;

    // Check if csr addr or mem addr; accordingly, get the msb bit.
    if (item.element_kind == UVM_REG) begin
      dv_base_reg csr;
      uvm_object rg = item.element;
      `downcast(csr, rg)
      msb = csr.get_msb_pos();
    end else if (item.element_kind == UVM_MEM) begin
      msb = DataWidth - 1;
    end else begin
      `uvm_fatal(`gfn, $sformatf("Unexpected address 0x%0h", rw.addr))
    end
    `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_req,
        a_opcode inside {PutFullData, PutPartialData};
        a_addr    == AddrWidth'(rw.addr);
        a_data    == DataWidth'(rw.data);
        a_mask[0] == 1;
        if (supports_byte_enable) {
          $countones(a_mask) > (msb / 8);
        } else {
          a_mask  == '1;
        })
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
  // not.
  if (!check_user_bit_idx("role", role_lsb, role_nbits)) role_nbits = 0;
  if (!check_user_bit_idx("uid", uid_lsb, uid_nbits)) uid_nbits = 0;

  this.role_lsb = role_lsb;
  this.role_nbits = role_nbits;
  this.uid_lsb = uid_lsb;
  this.uid_nbits = uid_nbits;
endfunction
