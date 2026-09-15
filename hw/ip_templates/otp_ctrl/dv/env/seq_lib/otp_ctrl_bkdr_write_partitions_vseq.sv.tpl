// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
from topgen.lib import Name

def get_part_items(part):
    has_digest = part["hw_digest"] or part["sw_digest"]
    match has_digest, part["zeroizable"]:
        case (True, True): return part["items"][:-2]
        case (False, False): return part["items"]
        case _: return part["items"][:-1]

buf_parts = [part for part in otp_mmap["partitions"] if part["variant"] == "Buffered"]
%>\

// This sequence provisions every buffered partition through the otp_ctrl_mem_bkdr_util_pkg
// helpers that top-level environments use to preload OTP, then triggers OTP initialization and
// checks that the hardware accepts the backdoor-written contents and digests.
//
// The scoreboard is disabled because the backdoor writes bypass its memory model; all checks are
// done within this sequence.
class otp_ctrl_bkdr_write_partitions_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_bkdr_write_partitions_vseq)

  `uvm_object_new

  virtual task pre_start();
    // OTP initialization is triggered from body() so that the wait for it is bounded.
    do_otp_pwr_init = 0;
    super.pre_start();
  endtask

  // Backdoor write random contents and the matching digest into every buffered partition once
  // the OTP array has been cleared.
  virtual task otp_ctrl_init();
% for part in buf_parts:
  % for item in get_part_items(part):
<%
item_name = Name.from_snake_case(item["name"])
%>\
    bit [${item_name.as_camel_case()}Size*8-1:0] ${item_name.as_snake_case()};
  % endfor
% endfor

    super.otp_ctrl_init();
% for part in buf_parts:
<%
part_name_snake = Name.from_snake_case(part["name"]).as_snake_case()
item_names = [Name.from_snake_case(item["name"]).as_snake_case()
              for item in get_part_items(part)]
%>\

  % for item_name in item_names:
    `DV_CHECK_STD_RANDOMIZE_FATAL(${item_name})
  % endfor
    otp_ctrl_mem_bkdr_util_pkg::otp_write_${part_name_snake}_partition(
        .mem_bkdr_util_h(cfg.mem_bkdr_util_h),
  % for item_name in item_names:
        .${item_name}(${item_name})${"" if loop.last else ","}
  % endfor
    );
% endfor
  endtask

  task body();
    bit [63:0] digest;

    // The hardware loads every buffered partition and checks its digest during initialization.
    // A failed check is fatal: every partition enters its error state and init done still
    // asserts, so a bad digest shows up in the error status read below.
    cfg.otp_ctrl_vif.drive_pwr_otp_init(1);
    `DV_WAIT(cfg.otp_ctrl_vif.pwr_otp_done_o == 1, "OTP initialization did not complete")
    cfg.otp_ctrl_vif.drive_pwr_otp_init(0);

    csr_rd_check(.ptr(ral.status.partition_error), .compare_value(0));
% for k, part in enumerate(otp_mmap["partitions"]):
  % if part["variant"] == "Buffered":
<%
part_name_snake = Name.from_snake_case(part["name"]).as_snake_case()
%>\
    csr_rd_check(.ptr(ral.partition_status_${k // 32}.${part_name_snake}_error), .compare_value(0));
  % endif
% endfor

    // The digest CSRs must expose the backdoor-written digests. A zero digest would pass unchecked,
    // since the hardware skips the integrity check of a blank digest.
% for part in buf_parts:
<%
part_name = Name.from_snake_case(part["name"])
%>\
    digest = cfg.mem_bkdr_util_h.read64(${part_name.as_camel_case()}DigestOffset);
    `DV_CHECK_NE(digest, 0)
    csr_rd_check(.ptr(ral.${part_name.as_snake_case()}_digest[0]), .compare_value(digest[31:0]));
    csr_rd_check(.ptr(ral.${part_name.as_snake_case()}_digest[1]), .compare_value(digest[63:32]));
% endfor
  endtask : body

endclass : otp_ctrl_bkdr_write_partitions_vseq
