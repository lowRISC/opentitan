// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Package partition metadata.
//
${gen_comment}
<%
from topgen.lib import Name
%>\
package otp_ctrl_part_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;

  ////////////////////////////////////
  // Scrambling Constants and Types //
  ////////////////////////////////////

  parameter int NumScrmblKeys = ${len(otp_mmap.config["scrambling"]["keys"])};
  parameter int NumDigestSets = ${len(otp_mmap.config["scrambling"]["digests"])};

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
% for key in otp_mmap.config["scrambling"]["keys"]:
    ${key["name"]}${"" if loop.last else ","}
% endfor
  } key_sel_e;

  typedef enum logic [ConstSelWidth-1:0] {
% for dig in otp_mmap.config["scrambling"]["digests"]:
    ${dig["name"]}${"" if loop.last else ","}
% endfor
  } digest_sel_e;

  // SEC_CM: SECRET.MEM.SCRAMBLE
  parameter key_array_t RndCnstKey = {
% for key in otp_mmap.config["scrambling"]["keys"][::-1]:
    ${"{0:}'h{1:0X}".format(otp_mmap.config["scrambling"]["key_size"] * 8, key["value"])}${"" if loop.last else ","}
% endfor
  };

  // SEC_CM: PART.MEM.DIGEST
  // Note: digest set 0 is used for computing the partition digests. Constants at
  // higher indices are used to compute the scrambling keys.
  parameter digest_const_array_t RndCnstDigestConst = {
% for dig in otp_mmap.config["scrambling"]["digests"][::-1]:
    ${"{0:}'h{1:0X}".format(otp_mmap.config["scrambling"]["cnst_size"] * 8, dig["cnst_value"])}${"" if loop.last else ","}
% endfor
  };

  parameter digest_iv_array_t RndCnstDigestIV = {
% for dig in otp_mmap.config["scrambling"]["digests"][::-1]:
    ${"{0:}'h{1:0X}".format(otp_mmap.config["scrambling"]["iv_size"] * 8, dig["iv_value"])}${"" if loop.last else ","}
% endfor
  };


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
  } part_info_t;

  parameter part_info_t PartInfoDefault = '{
      variant:          Unbuffered,
      offset:           '0,
      size:             OtpByteAddrWidth'('hFF),
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b0,
      write_lock:       1'b0,
      read_lock:        1'b0,
      integrity:        1'b0,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0
  };

  ////////////////////////
  // Partition Metadata //
  ////////////////////////

  localparam part_info_t PartInfo [NumPart] = '{
% for part in otp_mmap.config["partitions"]:
    // ${part["name"]}
    '{
      variant:          ${part["variant"]},
      offset:           ${otp_mmap.config["otp"]["byte_addr_width"]}'d${part["offset"]},
      size:             ${part["size"]},
      key_sel:          ${part["key_sel"] if part["key_sel"] != "NoKey" else "key_sel_e'('0)"},
      secret:           1'b${"1" if part["secret"] else "0"},
      sw_digest:        1'b${"1" if part["sw_digest"] else "0"},
      hw_digest:        1'b${"1" if part["hw_digest"] else "0"},
      write_lock:       1'b${"1" if part["write_lock"].lower() == "digest" else "0"},
      read_lock:        1'b${"1" if part["read_lock"].lower() == "digest" else "0"},
      integrity:        1'b${"1" if part["integrity"] else "0"},
      iskeymgr_creator: 1'b${"1" if part["iskeymgr_creator"] else "0"},
      iskeymgr_owner:   1'b${"1" if part["iskeymgr_owner"] else "0"}
    }${"" if loop.last else ","}
% endfor
  };

  typedef enum {
% for part in otp_mmap.config["partitions"]:
    ${Name.from_snake_case(part["name"]).as_camel_case()}Idx,
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
% for part in otp_mmap.config["partitions"]:
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

  // default value used for intermodule
  parameter otp_${part["name"].lower()}_data_t OTP_${part["name"].upper()}_DATA_DEFAULT = '{<% offset = part['offset'] + part['size'] %>
  % for k, item in enumerate(part["items"][::-1]):
    % if offset != item['offset'] + item['size']:
    unallocated: ${"{}'h{:0X}".format((offset - item['size'] - item['offset']) * 8, 0)}<% offset = item['offset'] + item['size'] %>,
    % endif
<%
  if item['ismubi']:
    item_cast_pre = "prim_mubi_pkg::mubi" + str(item["size"]*8) + "_t'("
    item_cast_post = ")"
  else:
    item_cast_pre = ""
    item_cast_post = ""
%>\
    ${item["name"].lower()}: ${item_cast_pre}${"{}'h{:0X}".format(item["size"] * 8, item["inv_default"])}${item_cast_post}${"," if k < len(part["items"])-1 else ""}<% offset -= item['size'] %>
  % endfor
  };
  % endif
% endfor
  typedef struct packed {
    // This reuses the same encoding as the life cycle signals for indicating valid status.
    lc_ctrl_pkg::lc_tx_t valid;
% for part in otp_mmap.config["partitions"][::-1]:
  % if part["bkout_type"]:
    otp_${part["name"].lower()}_data_t ${part["name"].lower()}_data;
  % endif
% endfor
  } otp_broadcast_t;

  // default value for intermodule
<%
  k = 0
  num_bkout = 0
  for part in otp_mmap.config["partitions"]:
    if part["bkout_type"]:
      num_bkout += 1
%>\
  parameter otp_broadcast_t OTP_BROADCAST_DEFAULT = '{
    valid: lc_ctrl_pkg::Off,
% for part in otp_mmap.config["partitions"][::-1]:
  % if part["bkout_type"]:
    ${part["name"].lower()}_data: OTP_${part["name"].upper()}_DATA_DEFAULT${"" if k == num_bkout-1 else ","}
<% k+=1 %>\
  % endif
% endfor
  };

<% offset =  int(otp_mmap.config["partitions"][-1]["offset"]) + int(otp_mmap.config["partitions"][-1]["size"]) %>
  // OTP invalid partition default for buffered partitions.
  parameter logic [${offset * 8 - 1}:0] PartInvDefault = ${offset * 8}'({
  % for k, part in enumerate(otp_mmap.config["partitions"][::-1]):
    ${int(part["size"])*8}'({
    % for item in part["items"][::-1]:
      % if offset != item['offset'] + item['size']:
      ${"{}'h{:0X}".format((offset - item['size'] - item['offset']) * 8, 0)}, // unallocated space<% offset = item['offset'] + item['size'] %>
      % endif
      ${"{}'h{:0X}".format(item["size"] * 8, item["inv_default"])}${("\n    })," if k < len(otp_mmap.config["partitions"])-1 else "\n    })});") if loop.last else ","}<% offset -= item['size'] %>
    % endfor
  % endfor

  ///////////////////////////////////////////////
  // Parameterized Assignment Helper Functions //
  ///////////////////////////////////////////////

  function automatic otp_ctrl_core_hw2reg_t named_reg_assign(
      logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest);
    otp_ctrl_core_hw2reg_t hw2reg;
    logic unused_sigs;
    unused_sigs = ^part_digest;
    hw2reg = '0;
% for k, part in enumerate(otp_mmap.config["partitions"]):
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
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
% for k, part in enumerate(otp_mmap.config["partitions"]):
  % if part["read_lock"] == "CSR":
    // ${part["name"]}
    if (!reg2hw.${part["name"].lower()}_read_lock) begin
<% part_name = Name.from_snake_case(part["name"]) %>\
      part_access_pre[${part_name.as_camel_case()}Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
  % endif
% endfor
    return part_access_pre;
  endfunction : named_part_access_pre

  function automatic otp_broadcast_t named_broadcast_assign(
      logic [NumPart-1:0] part_init_done,
      logic [$bits(PartInvDefault)/8-1:0][7:0] part_buf_data);
    otp_broadcast_t otp_broadcast;
    logic valid, unused;
    unused = 1'b0;
    valid = 1'b1;
% for part in otp_mmap.config["partitions"]:
    // ${part["name"]}
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
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
      logic [$bits(PartInvDefault)/8-1:0][7:0] part_buf_data,
      lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en);
    otp_keymgr_key_t otp_keymgr_key;
    logic valid, unused;
    unused = 1'b0;
    // For now we use a fixed struct type here so that the
    // interface to the keymgr remains stable. The type contains
    // a superset of all options, so we have to initialize it to '0 here.
    otp_keymgr_key = '0;
% for part in otp_mmap.config["partitions"]:
    // ${part["name"]}
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
  % if part["iskeymgr_creator"] or part["iskeymgr_owner"]:
    valid = (part_digest[${part_name_camel}Idx] != 0);
    % for item in part["items"]:
<%
  item_name = Name.from_snake_case(item["name"])
  item_name_camel = item_name.as_camel_case()
%>\
      % if item["iskeymgr_creator"] or item["iskeymgr_owner"]:
    otp_keymgr_key.${item["name"].lower()}_valid = valid;
    if (lc_ctrl_pkg::lc_tx_test_true_strict(lc_seed_hw_rd_en)) begin
      otp_keymgr_key.${item["name"].lower()} =
          part_buf_data[${item_name_camel}Offset +: ${item_name_camel}Size];
    end else begin
      otp_keymgr_key.${item["name"].lower()} =
          PartInvDefault[${item_name_camel}Offset*8 +: ${item_name_camel}Size*8];
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
