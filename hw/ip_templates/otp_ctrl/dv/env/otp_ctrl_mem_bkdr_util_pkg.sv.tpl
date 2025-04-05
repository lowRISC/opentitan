// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This package has functions that perform mem_bkdr_util accesses to different partitions in OTP.
// These functions end up performing reads and writes to the underlying simulated otp memory, so
// the functions must get a handle to the mem_bkdr_util instance for otp_ctrl as an argument.
//
// NB: this package is only suitable for top-level environments since it depends on SKU-dependent
// OTP ctrl fields.
<%
from topgen.lib import Name
%>
package otp_ctrl_mem_bkdr_util_pkg;

  import otp_ctrl_part_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_scrambler_pkg::*;

  function automatic void otp_write_lc_partition_state(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      lc_ctrl_state_pkg::lc_state_e lc_state
  );
    for (int i = 0; i < LcStateSize; i += 4) begin
      mem_bkdr_util_h.write32(i + LcStateOffset, lc_state[i*8+:32]);
    end
  endfunction : otp_write_lc_partition_state

  function automatic lc_ctrl_state_pkg::lc_state_e otp_read_lc_partition_state(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    lc_ctrl_state_pkg::lc_state_e lc_state;
    for (int i = 0; i < LcStateSize; i += 4) begin
      lc_state[i*8 +: 32] = mem_bkdr_util_h.read32(i + LcStateOffset);
    end

    return lc_state;
  endfunction : otp_read_lc_partition_state

  function automatic void otp_write_lc_partition_cnt(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      lc_ctrl_state_pkg::lc_cnt_e lc_cnt
  );
    for (int i = 0; i < LcTransitionCntSize; i += 4) begin
      mem_bkdr_util_h.write32(i + LcTransitionCntOffset, lc_cnt[i*8+:32]);
    end
  endfunction : otp_write_lc_partition_cnt

  function automatic void otp_write_lc_partition(mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
                                                 lc_ctrl_state_pkg::lc_cnt_e lc_cnt,
                                                 lc_ctrl_state_pkg::lc_state_e lc_state);

    otp_write_lc_partition_cnt(mem_bkdr_util_h, lc_cnt);
    otp_write_lc_partition_state(mem_bkdr_util_h, lc_state);
  endfunction : otp_write_lc_partition

  // The following steps are needed to backdoor write a non-secret partition:
  // 1). Backdoor write the input data to OTP memory.
  // 2). Calculate the correct digest for the secret partition.
  // 3). Backdoor write digest data to OTP memory.

  // The following steps are needed to backdoor write a secret partition:
  // 1). Scramble the RAW input data.
  // 2). Backdoor write the scrambled input data to OTP memory.
  // 3). Calculate the correct digest for the secret partition.
  // 4). Backdoor write digest data to OTP memory.

  // The HW_CFG1 partition needs to be a special case since it has items
  // smaller than 4 bytes and need to be concatenated. To make sure
  // this special case won't end up broken if the OTP layout changes
  // beyond what this supports the following checks are in place and
  // will cause a failure.
  // - No other partition except for HW_CFG1 has such small items.
  // - The small items in HW_CFG1 will be contained within 32 bits.

% for part in otp_mmap["partitions"]:
<%
if part["variant"] != "Buffered":
  continue
part_name = Name.from_snake_case(part["name"])
part_name_camel = part_name.as_camel_case()
part_name_snake = part_name.as_snake_case()
has_digest = part["hw_digest"] or part["sw_digest"]
part_items = part["items"][:-1] if has_digest else part["items"]
%>\
## Declare function and ports.
  function automatic void otp_write_${part_name_snake}_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
  % for item in part_items:
<%
item_name = Name.from_snake_case(item["name"])
sep = "" if loop.last else ","
%>\
      bit [${item_name.as_camel_case()}Size*8-1:0] ${item_name.as_snake_case()}${sep}
  % endfor
  );
    bit [${part_name_camel}DigestSize*8-1:0] digest;
    bit [bus_params_pkg::BUS_DW-1:0] partition_data[$];
  % if part_name_snake == "hw_cfg1":
##############################################
## Handle the hw_cfg1 partition.            ##
##############################################
<%
## Check that all small items are 1 byte, will fit in 32 bits, and are
## consecutive
weird_sized_items = [
    it for it in part_items if it["size"] != 1 and it["size"] % 4]
if weird_sized_items:
  weirds_string = (", ".join(f'{i["name"]} size {i["size"]}'
                   for i in weird_sized_items))
  raise ValueError(
      "In HW_CFG1 expected sizes of 1 or multiples of 4 bytes, got "
      "{weirds_string}")
item_sizes = [i["size"] for i in part_items]
ones_at = [i for i, s in enumerate(item_sizes) if s == 1]
consecutive = all(x2 - x1 == 1 for x1, x2 in zip(ones_at[:-1], ones_at[1:]))
if not consecutive:
  raise ValueError("non consecutive items with size 1 byte in HW_CFG1")
## Require all to fit in one word. Extend this if needed.
if len(ones_at) > 4:
  raise ValueError("Expected no more than 4 single byte in HW_CFG1")
%>\
##############################################
## Emit the hw_cfg1 partition's function body.
##############################################
    bit [bus_params_pkg::BUS_DW-1:0] concat_data[$];
    bit [31:0] word;

## Write all leading consecutive non-single byte variables.
% if ones_at[0] != 0:
  % for item in part_items[:ones_at[0]]:
<%
item_name = Name.from_snake_case(item["name"])
item_name_camel = item_name.as_camel_case()
item_name_snake = item_name.as_snake_case()
%>\
    for (int i = 0; i < ${item_name_camel}Size; i += 4) begin
      mem_bkdr_util_h.write32(i + ${item_name_camel}Offset, ${item_name_snake}[i*8+:32]);
      concat_data.push_front(${item_name_snake}[i*8+:32]);
    end
  % endfor
% endif
## Concatenate all single-byte variables into a word in descending order and
## write the value.
    word = {
% for i in list(reversed(ones_at)):
<%
item_name = Name.from_snake_case(part_items[i]["name"])
sep = "" if loop.last else ","
%>\
      ${item_name.as_snake_case()}${sep}
% endfor
    };
## Write the word.
<%
first_item_name = Name.from_snake_case(part_items[ones_at[0]]["name"])
first_item_name_camel = first_item_name.as_camel_case()
%>\
    mem_bkdr_util_h.write32(${ones_at[0]} + ${first_item_name_camel}Offset, word);
    concat_data.push_front(word);

## Write all trailing consecutive non-single byte variables.
% if ones_at[-1] < len(part_items) - 1:
  % for item in part_items[ones_at[-1] + 1:]:
<%
item_name = Name.from_snake_case(item["name"])
item_name_camel = item_name.as_camel_case()
item_name_snake = item_name.as_snake_case()
%>\
    for (int i = 0; i < ${item_name_camel}Size; i += 4) begin
      mem_bkdr_util_h.write32(i + ${item_name_camel}Offset, ${item_name_snake}[i*8+:32]);
      concat_data.push_front(${item_name_snake}[i*8+:32]);
    end
  % endfor
% endif
    partition_data = {<<32{concat_data}};
    digest = cal_digest(${part_name_camel}Idx, partition_data);
    mem_bkdr_util_h.write64(${part_name_camel}DigestOffset, digest);
  endfunction

## Done with HW_CFG1
##
  % else:
##################################################
## Handle other buffered partitions.            ##
##################################################
    % if part["secret"]:
#############################################
## Emit the secret partition's function body.
#############################################
## Declare variables to hold scrambled data.
      % for item in part_items:
<%
if item["size"] < 4:
  raise ValueError(
      f"Unexpected item {item['name']} smaller than 4 bytes in partition {part['name']}")
item_name = Name.from_snake_case(item["name"])
item_name_camel = item_name.as_camel_case()
item_name_snake = item_name.as_snake_case()
%>\
    bit [${item_name.as_camel_case()}Size*8-1:0] scrambled_${item_name.as_snake_case()};
      % endfor
    % endif

    % for item in part_items:
<%
item_name = Name.from_snake_case(item["name"])
item_name_camel = item_name.as_camel_case()
item_name_snake = item_name.as_snake_case()
%>\
      % if part["secret"]:
    for (int i = 0; i < ${item_name_camel}Size; i += 8) begin
      scrambled_${item_name.as_snake_case()}[i*8+:64] = scramble_data(
          ${item_name_snake}[i*8+:64], ${part_name_camel}Idx);
      mem_bkdr_util_h.write64(i + ${item_name_camel}Offset,
                              scrambled_${item_name.as_snake_case()}[i*8+:64]);
    end
      % else:
    for (int i = 0; i < ${item_name_camel}Size; i += 4) begin
      mem_bkdr_util_h.write32(i + ${item_name_camel}Offset, ${item_name_snake}[i*8+:32]);
    end
      % endif
    % endfor

    partition_data = {<<32{
    % for item in list(reversed(part_items)):
<%
item_name = Name.from_snake_case(item["name"])
sep = "" if loop.last else ","
%>\
      % if part["secret"]:
      scrambled_${item_name.as_snake_case()}${sep}
      % else:
      ${item_name.as_snake_case()}${sep}
      % endif
    % endfor
    }};
    digest = cal_digest(${part_name_camel}Idx, partition_data);
    mem_bkdr_util_h.write64(${part_name_camel}DigestOffset, digest);
  endfunction

  % endif
% endfor
  // Functions that clear the provisioning state of the buffered partitions.
  // This is useful in tests that make front-door accesses for provisioning purposes.
% for part in otp_mmap["partitions"]:
  % if part["variant"] == "Buffered":
<%
part_name = Name.from_snake_case(part["name"])
part_name_camel = part_name.as_camel_case()
part_name_snake = part_name.as_snake_case()
%>\
  function automatic void otp_clear_${part_name_snake}_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    for (int i = 0; i < ${part_name_camel}Size; i += 4) begin
      mem_bkdr_util_h.write32(i + ${part_name_camel}Offset, 32'h0);
    end
  endfunction

  % endif
% endfor
endpackage : otp_ctrl_mem_bkdr_util_pkg
