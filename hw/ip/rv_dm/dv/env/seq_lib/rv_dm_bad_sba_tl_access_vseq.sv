// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drive random traffic out the SBA TL interface with more weightage on accesses that will result
// in sberror begin flagged.
class rv_dm_bad_sba_tl_access_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_bad_sba_tl_access_vseq)
  `uvm_object_new

  // Ocassionally send bad SBA addresses.
  virtual function void randomize_req(sba_access_item req);
    bit bad_sba = $urandom_range(0, 9) > 2; // 70%
    req.disable_rsp_randomization();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        autoincrement == 0;
        if (bad_sba) {
          // Create unsupported size or unaligned address error cases.
          (size > SbaAccessSize32b) || ((addr % (1 << size)) != 0);
        } else {
          size <= SbaAccessSize32b;
          (addr % (1 << size)) == 0;
        }
    )
    override_req_to_read_addr_after_write(req);
  endfunction

endclass
