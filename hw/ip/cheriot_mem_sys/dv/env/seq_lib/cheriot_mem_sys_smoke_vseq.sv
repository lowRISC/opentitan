// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Smoke test in ePMP mode. Each round writes TBRE_START, which the revocation engine must ignore
// apart from setting TBRE_STATUS.start_err.
class cheriot_mem_sys_smoke_vseq extends cheriot_mem_sys_base_vseq;
  `uvm_object_utils(cheriot_mem_sys_smoke_vseq)

  typedef enum bit [1:0] {
    InMainSram,
    InNvm,
    Anywhere
  } addr_kind_e;

  rand int unsigned num_rounds;
  rand addr_kind_e  addr_kind;
  rand bit [31:0]   base_addr;
  rand bit [31:0]   num_caps;

  constraint num_rounds_c {
    num_rounds inside {[1:10]};
  }

  // Mostly starts that CHERIoT mode would accept (the regions are applied in body())
  constraint addr_kind_c {
    addr_kind dist {
      InMainSram :/ 4,
      InNvm      :/ 4,
      Anywhere   :/ 2
    };
  }

  constraint num_caps_c {
    num_caps dist {
      [1 : 64]             :/ 8,
      0                    :/ 1,
      [65 : 32'hffff_ffff] :/ 1
    };
  }

  `uvm_object_new

  task body();
    // Reset state of the revocation engine
    csr_rd_check(.ptr(ral.tbre_regwen), .compare_value(1));
    csr_rd_check(.ptr(ral.tbre_status), .compare_value(0));
    csr_rd_check(.ptr(ral.tbre_epoch), .compare_value(0));

    // Enable tbre_done so that any interrupt shows on the pin
    csr_wr(.ptr(ral.intr_enable), .value(1));

    for (int unsigned i = 0; i < num_rounds; i++) begin
      // The first start is always one CHERIoT mode would accept.
      `DV_CHECK_FATAL(randomize(addr_kind, base_addr, num_caps) with {
          addr_kind == InMainSram -> base_addr inside {[cfg.tagged_regions.main_sram_base :
                                                       cfg.tagged_regions.main_sram_top - 8]};
          addr_kind == InNvm      -> base_addr inside {[cfg.tagged_regions.nvm_base :
                                                       cfg.tagged_regions.nvm_top - 8]};
          i == 0 -> (addr_kind != Anywhere && num_caps inside {[1:64]});
        })
      `uvm_info(`gfn, $sformatf("Round %0d/%0d: start at 0x%08x (%s), %0d capabilities", i + 1,
                                num_rounds, base_addr, addr_kind.name(), num_caps), UVM_MEDIUM)

      // The sweep registers are writable while the engine is inactive. The register model
      // masks the read-back to the implemented bits.
      csr_wr(.ptr(ral.tbre_base_addr), .value(base_addr));
      csr_wr(.ptr(ral.tbre_num_caps), .value(num_caps));
      csr_rd_check(.ptr(ral.tbre_base_addr), .compare_vs_ral(1));
      csr_rd_check(.ptr(ral.tbre_num_caps), .compare_vs_ral(1));

      // The start is ignored: start_err, no sweep, no epoch change, no interrupt.
      csr_wr(.ptr(ral.tbre_start), .value(1));
      csr_rd_check(.ptr(ral.tbre_status.start_err), .compare_value(1));
      csr_rd_check(.ptr(ral.tbre_status.busy), .compare_value(0));
      csr_rd_check(.ptr(ral.tbre_status.sweep_err), .compare_value(0));
      csr_rd_check(.ptr(ral.tbre_regwen), .compare_value(1));
      csr_rd_check(.ptr(ral.tbre_epoch), .compare_value(0));
      csr_rd_check(.ptr(ral.intr_state), .compare_value(0));
      `DV_CHECK_EQ(cfg.intr_vif.pins[0], 1'b0, "tbre_done interrupt pin raised")

      // start_err is write-1-to-clear
      csr_wr(.ptr(ral.tbre_status), .value(1 << ral.tbre_status.start_err.get_lsb_pos()));
      csr_rd_check(.ptr(ral.tbre_status), .compare_value(0));
    end
  endtask : body

endclass : cheriot_mem_sys_smoke_vseq
