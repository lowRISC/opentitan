// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Package partition metadata.
//
<%
from topgen.lib import Name
%>\
package otp_ctrl_part_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_top_specific_pkg::*;

  ////////////////////////////////////
  // Scrambling Constants and Types //
  ////////////////////////////////////

  parameter int NumScrmblKeys = ${otp_mmap["scrambling"]["num_keys"]};
  parameter int NumDigestSets = ${otp_mmap["scrambling"]["num_digests"]};

  parameter int ScrmblKeySelWidth = vbits(NumScrmblKeys);
  parameter int DigestSetSelWidth = vbits(NumDigestSets);
  parameter int ConstSelWidth = (ScrmblKeySelWidth > DigestSetSelWidth) ?
                                ScrmblKeySelWidth :
                                DigestSetSelWidth;

  typedef enum logic [ConstSelWidth-1:0] {
    StandardMode,
    ChainedMode
  } digest_mode_e;

  typedef logic [NumScrmblKeys-1:0][ScrmblKeyWidth-1:0] key_array_t;
  typedef logic [NumDigestSets-1:0][ScrmblKeyWidth-1:0] digest_const_array_t;
  typedef logic [NumDigestSets-1:0][ScrmblBlockWidth-1:0] digest_iv_array_t;

  typedef enum logic [ConstSelWidth-1:0] {
% for key in otp_mmap["scrambling"]["keys"]:
    ${key["name"]}${"" if loop.last else ","}
% endfor
  } key_sel_e;

  typedef enum logic [ConstSelWidth-1:0] {
% for dig in otp_mmap["scrambling"]["digests"]:
    ${dig["name"]}${"" if loop.last else ","}
% endfor
  } digest_sel_e;

  /////////////////////////////////////
  // Typedefs for Partition Metadata //
  /////////////////////////////////////

  typedef enum logic [1:0] {
    Unbuffered,
    Buffered,
    LifeCycle
  } part_variant_e;

  typedef struct packed {
    part_variant_e variant;
    // Offset and size within the OTP array, in Bytes.
    logic [OtpByteAddrWidth-1:0] offset;
    logic [OtpByteAddrWidth-1:0] size;
    // Key index to use for scrambling.
    key_sel_e key_sel;
    // Attributes
    logic secret;           // Whether the partition is secret (and hence scrambled)
    logic sw_digest;        // Whether the partition has a software digest
    logic hw_digest;        // Whether the partition has a hardware digest
    logic write_lock;       // Whether the partition is write lockable (via digest)
    logic read_lock;        // Whether the partition is read lockable (via digest)
    logic integrity;        // Whether the partition is integrity protected
    logic iskeymgr_creator; // Whether the partition has any creator key material
    logic iskeymgr_owner;   // Whether the partition has any owner key material
    logic zeroizable;       // Whether the partition can be zeroized
    logic ignore_read_lock_in_rma; // Whether the partition can always be read in the RMA LC state
  } part_info_t;

  parameter part_info_t PartInfoDefault = '{
      variant:                 Unbuffered,
      offset:                  '0,
      size:                    OtpByteAddrWidth'('hFF),
      key_sel:                 key_sel_e'('0),
      secret:                  1'b0,
      sw_digest:               1'b0,
      hw_digest:               1'b0,
      write_lock:              1'b0,
      read_lock:               1'b0,
      integrity:               1'b0,
      iskeymgr_creator:        1'b0,
      iskeymgr_owner:          1'b0,
      zeroizable:              1'b0,
      ignore_read_lock_in_rma: 1'b0
  };

  ////////////////////////
  // Partition Metadata //
  ////////////////////////

  localparam part_info_t PartInfo [NumPart] = '{
% for part in otp_mmap["partitions"]:
    // ${part["name"]}
    '{
      variant:          ${part["variant"]},
      offset:           ${otp_mmap["otp"]["byte_addr_width"]}'d${part["offset"]},
      size:             ${part["size"]},
      key_sel:          ${part["key_sel"] if part["key_sel"] != "NoKey" else "key_sel_e'('0)"},
      secret:           1'b${"1" if part["secret"] else "0"},
      sw_digest:        1'b${"1" if part["sw_digest"] else "0"},
      hw_digest:        1'b${"1" if part["hw_digest"] else "0"},
      write_lock:       1'b${"1" if part["write_lock"].lower() == "digest" else "0"},
      read_lock:        1'b${"1" if part["read_lock"].lower() == "digest" else "0"},
      integrity:        1'b${"1" if part["integrity"] else "0"},
      iskeymgr_creator: 1'b${"1" if part["iskeymgr_creator"] else "0"},
      iskeymgr_owner:   1'b${"1" if part["iskeymgr_owner"] else "0"},
      zeroizable:       1'b${"1" if part["zeroizable"] else "0"},
      ignore_read_lock_in_rma: 1'b${"1" if part["ignore_read_lock_in_rma"] else "0"}
    }${"" if loop.last else ","}
% endfor
  };

  typedef enum {
% for part in otp_mmap["partitions"]:
    ${Name.to_camel_case(part["name"])}Idx,
% endfor
    // These are not "real partitions", but in terms of implementation it is convenient to
    // add these at the end of certain arrays.
    DaiIdx,
    LciIdx,
    KdiIdx,
    // Number of agents is the last idx+1.
    NumAgentsIdx
  } part_idx_e;

  parameter int NumAgents = int'(NumAgentsIdx);

  // Breakout types for easier access of individual items.
% for part in otp_mmap["partitions"]:
  % if part["bkout_type"]:
  typedef struct packed {<% offset = part['offset'] + part['size'] %>
    % for item in part["items"][::-1]:
      % if offset != item['offset'] + item['size']:
    logic [${(offset - item['size'] - item['offset']) * 8 - 1}:0] unallocated;<% offset = item['offset'] + item['size'] %>
      % endif
<%
  if item['ismubi']:
    item_type = 'prim_mubi_pkg::mubi' + str(item["size"]*8) + '_t'
  else:
    item_type = 'logic [' + str(int(item["size"])*8-1) + ':0]'
%>\
    ${item_type} ${item["name"].lower()};<% offset -= item['size'] %>
    % endfor
  } otp_${part["name"].lower()}_data_t;
  % endif
% endfor

  typedef struct packed {
    // This reuses the same encoding as the life cycle signals for indicating valid status.
    lc_ctrl_pkg::lc_tx_t valid;
% for part in otp_mmap["partitions"][::-1]:
  % if part["bkout_type"]:
    otp_${part["name"].lower()}_data_t ${part["name"].lower()}_data;
  % endif
% endfor
  } otp_broadcast_t;

  ///////////////////////////////////////////////
  // Parameterized Assignment Helper Functions //
  ///////////////////////////////////////////////

  function automatic otp_ctrl_core_hw2reg_t named_reg_assign(
      logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest);
    otp_ctrl_core_hw2reg_t hw2reg;
    logic unused_sigs;
    unused_sigs = ^part_digest;
    hw2reg = '0;
% for k, part in enumerate(otp_mmap["partitions"]):
<%
  part_name_camel = Name.to_camel_case(part["name"])
%>\
  % if part["sw_digest"] or part["hw_digest"]:
    hw2reg.${part["name"].lower()}_digest = part_digest[${part_name_camel}Idx];
  % endif
% endfor
    return hw2reg;
  endfunction : named_reg_assign

  function automatic part_access_t [NumPart-1:0] named_part_access_pre(
      otp_ctrl_core_reg2hw_t reg2hw);
    part_access_t [NumPart-1:0] part_access_pre;
    logic unused_sigs;
    unused_sigs = ^reg2hw;
    // Default (this will be overridden by partition-internal settings).
    part_access_pre = {{32'(2*NumPart)}{prim_mubi_pkg::MuBi8False}};
    // Note: these could be made a MuBi CSRs in the future.
    // The main thing that is missing right now is proper support for W0C.
% for k, part in enumerate(otp_mmap["partitions"]):
  % if part["read_lock"] == "CSR":
    // ${part["name"]}
    if (!reg2hw.${part["name"].lower()}_read_lock) begin
      part_access_pre[${Name.to_camel_case(part["name"])}Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
  % endif
% endfor
    return part_access_pre;
  endfunction : named_part_access_pre

<% offset = int(otp_mmap["partitions"][-1]["offset"]) + int(otp_mmap["partitions"][-1]["size"]) %>\
  function automatic otp_broadcast_t named_broadcast_assign(
      logic [NumPart-1:0] part_init_done,
      logic [${offset-1}:0][7:0] part_buf_data);
    otp_broadcast_t otp_broadcast;
    logic valid, unused;
    unused = 1'b0;
    valid = 1'b1;
% for part in otp_mmap["partitions"]:
    // ${part["name"]}
<%
  part_name_camel = Name.to_camel_case(part["name"])
%>\
  % if part["bkout_type"]:
    valid &= part_init_done[${part_name_camel}Idx];
    otp_broadcast.${part["name"].lower()}_data = otp_${part["name"].lower()}_data_t'(part_buf_data[${part_name_camel}Offset +: ${part_name_camel}Size]);
  % else:
    unused ^= ^{part_init_done[${part_name_camel}Idx],
                part_buf_data[${part_name_camel}Offset +: ${part_name_camel}Size]};
  % endif
% endfor
    otp_broadcast.valid = lc_ctrl_pkg::lc_tx_bool_to_lc_tx(valid);
    return otp_broadcast;
  endfunction : named_broadcast_assign

  function automatic otp_keymgr_key_t named_keymgr_key_assign(
      logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest,
      logic [${offset-1}:0][7:0] part_buf_data,
      logic [${offset*8-1}:0] part_inv_default,
      lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en);
    otp_keymgr_key_t otp_keymgr_key;
    logic valid, unused;
    unused = 1'b0;
    // For now we use a fixed struct type here so that the
    // interface to the keymgr remains stable. The type contains
    // a superset of all options, so we have to initialize it to '0 here.
    otp_keymgr_key = '0;
% for part in otp_mmap["partitions"]:
    // ${part["name"]}
<%
  part_name_camel = Name.to_camel_case(part["name"])
%>\
  % if part["iskeymgr_creator"] or part["iskeymgr_owner"]:
    valid = (part_digest[${part_name_camel}Idx] != 0);
    % for item in part["items"]:
<%
  item_name_camel = Name.to_camel_case(item["name"])
%>\
      % if item["iskeymgr_creator"] or item["iskeymgr_owner"]:
    otp_keymgr_key.${item["name"].lower()}_valid = valid;
    if (lc_ctrl_pkg::lc_tx_test_true_strict(lc_seed_hw_rd_en)) begin
      otp_keymgr_key.${item["name"].lower()} =
          part_buf_data[${item_name_camel}Offset +: ${item_name_camel}Size];
    end else begin
      otp_keymgr_key.${item["name"].lower()} =
          part_inv_default[${item_name_camel}Offset*8 +: ${item_name_camel}Size*8];
    end
      % else:
        % if not item["isdigest"]:
    unused ^= ^part_buf_data[${item_name_camel}Offset +: ${item_name_camel}Size];
        % endif
      % endif
    % endfor
    // This is not used since we consume the
    // ungated digest values from the part_digest array.
    unused ^= ^part_buf_data[${part_name_camel}DigestOffset +: ${part_name_camel}DigestSize];
  % else:
    unused ^= ^{part_digest[${part_name_camel}Idx],
                part_buf_data[${part_name_camel}Offset +: ${part_name_camel}Size]};
  % endif
% endfor
    unused ^= valid;
    return otp_keymgr_key;
  endfunction : named_keymgr_key_assign

endpackage : otp_ctrl_part_pkg
