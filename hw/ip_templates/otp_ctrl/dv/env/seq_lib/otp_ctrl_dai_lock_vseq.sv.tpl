// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gen_comment}
<%
from topgen.lib import Name

parts_without_lc = [part for part in otp_mmap.config["partitions"] if
                    part["variant"] in ["Buffered", "Unbuffered"]]

parts_with_digest = [part for part in otp_mmap.config["partitions"] if
                     (part["sw_digest"] or part["hw_digest"])]
%>\
// otp_ctrl_dai_lock_vseq is developed to read/write lock DAI interface by partitions, and request
// read/write access to check if correct status and error code is triggered

// Partition's legal range covers offset to digest addresses, dai_rd/dai_wr function will
// randomize the address based on the granularity.
`define PART_ADDR_RANGE(i) ${"\\"}
    {[PartInfo[``i``].offset : (PartInfo[``i``].offset + PartInfo[``i``].size - 8)]}

class otp_ctrl_dai_lock_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_dai_lock_vseq)

  `uvm_object_new

  // enable access_err for each cycle
  constraint no_access_err_c {access_locked_parts == 1;}

  constraint num_trans_c {
    num_trans  inside {[1:10]};
    num_dai_op inside {[1:50]};
  }

  // the LC partition is always the last one
  constraint partition_index_c {part_idx inside {[0:LifeCycleIdx]};}

  constraint dai_wr_legal_addr_c {
% for part in parts_without_lc:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
    if (part_idx == ${part_name_camel}Idx) {
      dai_addr inside `PART_ADDR_RANGE(${part_name_camel}Idx);
    }
% endfor
    if (part_idx == LifeCycleIdx) {
      if (write_unused_addr) {
        dai_addr inside {[PartInfo[LifeCycleIdx].offset : {OTP_ADDR_WIDTH{1'b1}}]};
      } else {
        dai_addr inside `PART_ADDR_RANGE(LifeCycleIdx);
      }
    }
    solve part_idx before dai_addr;
  }

  constraint dai_wr_digests_c {
    {dai_addr[TL_AW-1:2], 2'b0} dist {
      {
% for part in parts_with_digest:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
        ${part_name_camel}DigestOffset${"" if loop.last else ","}
% endfor
      } :/ 1,
      [VendorTestOffset : '1] :/ 9
    };
  }

  virtual task pre_start();
    super.pre_start();
    is_valid_dai_op = 0;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if ($urandom_range(0, 1)) begin
      cfg.otp_ctrl_vif.drive_lc_creator_seed_sw_rw_en(get_rand_lc_tx_val(.t_weight(0)));
    end
    if ($urandom_range(0, 1)) begin
      cfg.otp_ctrl_vif.drive_lc_owner_seed_sw_rw_en(get_rand_lc_tx_val(.t_weight(0)));
    end
  endtask

endclass

`undef PART_ADDR_RANGE
