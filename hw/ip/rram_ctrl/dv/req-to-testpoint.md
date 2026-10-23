# rram_ctrl: requirement to testpoint mapping

This file maps the [requirements](requirements.md) to the way that the requirement will be tested.
There are four lists of places these requirements can be tracked:
- UVM covergroups (**CG**), also listed in the [testplan](../data/rram_ctrl_testplan.hjson)).
- UVM tests (**UVM**), which address a list of testpoints in a [testplan](../data/rram_ctrl_testplan.hjson)).
- Testpoints (**SEC**) (also UVM tests) that are specific to security countermeasures in a [sec_cm testplan](../data/rram_ctrl_sec_cm_testplan.hjson).
- The [FPV test properties](formal/property_list.md) (**FPV**).

The list in this file is in the same order as [requirements](requirements.md).

## 1. Memory organisation and address map

- **1.1**: The RRAM has two separately-addressed partitions: **data** and **info**.

  Addressed by:
  - `smoke` (**UVM**)

- **1.2**: The first `NumDataPages - NumOtpPages` pages of the data partition contain general-purpose data.

  To test this, we must see accesses to each end (pages 0 and 4089), plus an access to an interior page.
  These three types of access must be seen from each of the three sources (host, SW and lcmgr-hw-if).

  Addressed by:
  - `data_page_access_cg` (**CG**)
  - `smoke` (**UVM**)
  - `sw_op` (**UVM**)

- **1.3**: Page `NumDataPages - NumOtpPages` of the data partition holds OTP integrity words.

  To test this, we must see accesses to the page through otp-hw-if that succeed.
  We must also see attempted accesses from the host and SW sources (which will fail with a memory protection error).

  Addressed by:
  - `otp_page_access_cg` (**CG**)
  - `rewrite_op` (**UVM**)
  - `otp_standalone` (**UVM**)
  - `otp_write_blank_err` (**UVM**)

- **1.4**: The last `NumOtpPages-1` pages of the data partition hold OTP data.

  To test this, we must see successful accesses through otp-hw-if to each of the `NumOtpPages-1` pages.
  We must also see attempted accesses to the top page from the host and SW sources (which will fail with a memory protection error).
  We must also see that the RMA wipe doesn't touch any of these pages.

  Addressed by:
  - `otp_page_access_cg` (**CG**)
  - `otp_region_protection` (**UVM**)
  - `otp_standalone` (**UVM**)
  - `rma` (**UVM**)

- **1.5**: Info partition: `NumInfoPages` pages, accessible by SW and lcmgr-hw-if only (never the host).

  To test this, we must see access to info pages 0, 5, 6 and 7 (minimum and maximum, and each named info page).
  This must be seen for both SW and lcmgr-hw-if.
  We must also see failed access to an info page through `host_tl`.

  Addressed by:
  - `info_page_access_cg` (**CG**)
  - `smoke` (**UVM**)
  - `sw_op` (**UVM**)
  - `seed_partition` (**UVM**)
  - `isolated_partition` (**UVM**)
  - `seed_read` (**UVM**)

- **1.6**: There are `NumEmulInfoRegions` windows with emulated info pages on the data partition.

  This can be checked in two ways: FPV and functional simulation.
  As such, we will address them with FPV and also stimulate the behaviour with UVM tests.
  We won't track those tests with a covergroup: the exhaustive testing is done by FPV.

  For a functional simulation, we should see multiple subregions in use, some locked.
  Those subregions will have different access permissions, which can be checked.
  The functional simulation will then also see attempted accesses to the subregions, which will be denied.

  Addressed by:
  - (---) (**FPV**)
  - `emul_info_window` (**UVM**)
  - `emul_info_window_overlap` (**UVM**)
  - `emul_info_subregion` (**UVM**)
  - `emul_info_permissions` (**UVM**)

- **1.7**: Address granularity (byte-addressed).

  Addressed by:
  - `sw_op` (**UVM**)
  - `host_read_direct` (**UVM**)

## 2. Bus interfaces (TL-UL)

- **2.1**: `core_tl` is a TL-UL device interface carrying registers, FIFO windows and SW transactions.

  To see the requirement being tested, we should see each type of access through `core_tl`.
  This will almost certainly be covered when testing the other requirements.
  As such, it can be tracked with a single UVM covergroup.

  Addressed by:
  - `core_tl_cg` (**CG**)
  - `smoke` (**UVM**)
  - `csr_rw` (**UVM**)
  - `tl_d_oob_addr_access` (**UVM**)
  - `tl_d_illegal_access` (**UVM**)
  - `tl_d_outstanding_access` (**UVM**)
  - `tl_d_partial_access` (**UVM**)

- **2.2**: `host_tl` is read-only and limited to the data partition; it cannot reach the info partition or the OTP region.

  The positive part of the requirement says that `host_tl` can perform reads from the data partition.
  This can be tested by functional simulation.
  The negative part says that the interface is read-only and can only target the data partition.
  This is more amenable to FPV.

  Addressed by:
  - (---) (**FPV**)
  - `host_read_direct` (**UVM**)
  - `otp_region_protection` (**UVM**)

- **2.3**: Two separate FIFO access windows, with bus back-pressure when the write FIFO is full or the read FIFO is empty.

  These windows can be easily checked with functional verification.
  The covergroup will check that we see the back-pressure.

  Addressed by:
  - `fifo_backpressure_cg` (**CG**)
  - `fifo_lvl_cg` (**CG**)
  - `sw_op` (**UVM**)
  - `interrupts` (**UVM**)

- **2.4**: `wr_fifo` is write-only, `rd_fifo` is read-only; both are single-word windows without byte writes.

  This is most easily checked with FPV.
  There will be properties to check that writes/reads the wrong way and partial writes are rejected.

  Addressed by:
  - (---) (**FPV**)

- **2.5**: `wr_fifo` writes with no operation in progress are discarded without error; with RRAM disabled they return a TL-UL error.

  This is most easily checked with FPV.

  Addressed by:
  - (---) (**FPV**)

- **2.6**: Host reads carry integrity from `rram_phy_rd`; address infection is removed in `u_tl_adapter_host`.

  This covers the countermeasure `MEM.ADDR_INFECTION`.

  Any read through `host_tl` will stimulate this.
  In the UVM environment, the added integrity is checked in `cip_base_scoreboard`.
  The removal of address infection is checked by any check of the data that was read.

  Addressed by:
  - `smoke` (**UVM**)
  - `host_read_direct` (**UVM**)
  - `sec_cm_host_bus_integrity` (**SEC**)
  - `sec_cm_mem_addr_infection` (**SEC**)

- **2.7**: TL-UL gating primitives (`HOST_TL_LC_GATE`, `WR_TL_LC_GATE`) have sparse FSMs.

  This is checked by a `sec_cm` fault-injection test.

  Addressed by:
  - `sec_cm_fsm_sparse` (**SEC**)

- **2.8**: Command integrity is checked on both `core_tl` and `host_tl`.

  This covers the countermeasures `REG.BUS.INTEGRITY` and `HOST.BUS.INTEGRITY`.

  Addressed by:
  - `tl_intg_err` (**UVM**)
  - `sec_cm_reg_bus_integrity` (**SEC**)
  - `sec_cm_host_bus_integrity` (**SEC**)

- **2.9**: Host reads are subject to memory protection.

  The checks are stimulated by UVM tests, but making sure all corners are covered is easier with FPV.

  Addressed by:
  - (---) (**FPV**)
  - `smoke` (**UVM**)
  - `memory_protection` (**UVM**)
  - `otp_region_protection` (**UVM**)
  - `emul_info_window` (**UVM**)
  - `emul_info_window_overlap` (**UVM**)

- **2.10**: Host read error responses (correctable errors fixed and reported; uncorrectable errors give a TL-UL error).

  Addressed by:
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

## 3. Software operation interface (CONTROL / ADDR / FIFOs)

- **3.1**: Supported ops are `Read`, `Write` and `Rewrite`; other values give `ERR_CODE.op_err`.

  The supported operations get stimulated by `sw_op` and `rewrite_op`.
  The rejection of unsupported operations is easy to check with FPV.

  Addressed by:
  - (---) (**FPV**)
  - `sw_op` (**UVM**)
  - `rewrite_op` (**UVM**)

- **3.2**: `CONTROL.NUM` is the number of bus words minus 1 (max 1024); it is ignored for a `Rewrite`.

  See `CONTROL.NUM` for each size (values 0..1023) for each operation.
  This will have no effect for `Rewrite` it should be given different values to check they have no effect.

  Addressed by:
  - `control_cg` (**CG**)
  - `sw_op` (**UVM**)
  - `rewrite_op` (**UVM**)

- **3.3**: Writing 1 to `CONTROL.START`, starts an RRAM transaction.

  This is triggered by any SW operation.

  Addressed by:
  - `sw_op` (**UVM**)

- **3.4**: Write / Rewrite operation size and alignment

  See Write and Rewrite operations with base addresses that are not RRAM-word (16 B) aligned.
  See Write operations with incorrect lengths (if `CONTROL.NUM` is not 3 mod 4).
  In each case, check that RRAM is not modified and that `OP_STATUS.err` and `ERR_CODE.op_err` are set when the operation completes.

  Addressed by:
  - `write_size_cg` (**CG**)
  - `sw_op_addr_cg` (**CG**)
  - `sw_err_cg` (**CG**)
  - `sw_op` (**UVM**)
  - `rewrite_op` (**UVM**)

- **3.5**: `ADDR.START` is truncated to a bus word for reads.

  See reads with misaligned addresses (which get truncated to a bus word).

  Addressed by:
  - `sw_op_addr_cg` (**CG**)
  - `sw_op` (**UVM**)

- **3.6**: `CTRL_REGWEN.EN` is HW-controlled and locks `CONTROL`/`ADDR` during an operation.

  This covers the countermeasure `CTRL.CONFIG.REGWEN`.

  This is also required by the countermeasure `CTRL.CONFIG.REGWEN`.
  It is best addressed by FPV, which should check that:
  - The REGWEN signal is false during an operation.
  - When that REGWEN signal is false, writes to `CONTROL` and `ADDR` are rejected.

  For an extra layer of confidence, there is also a UVM covergroup.
  We probably expect to cover this with UVM tests addressing other requirements.

  Addressed by:
  - (---) (**FPV**)
  - `regwen_val_when_new_value_written_cg` (**CG**)

- **3.7**: `OP_STATUS.done` and `.err` are set by HW and cleared by SW.

  Addressed by:
  - `op_status_cg` (**CG**)
  - `smoke` (**UVM**)
  - `sw_op` (**UVM**)
  - `error_invalid_op` (**UVM**)
  - `rma_sw_dis` (**UVM**)

- **3.8**: `INTR_STATE.op_done` signals completion of Read, Write and Rewrite.

  The interrupt itself is most easily tested by FPV (which has more detail in section 10).
  The properties will cover the fact that the interrupt line reflects the state (if the interrupt is enabled).
  There will also be properties to check the state gets set at the end of any of the three operations.
  The behaviour is also seen in some UVM tests.

  Addressed by:
  - (---) (**FPV**)
  - `sw_op` (**UVM**)
  - `interrupts` (**UVM**)

- **3.9**: `FIFO_LVL.WR`/`FIFO_LVL.RD` set the `wr_lvl`/`rd_lvl` interrupt watermarks.

  This is most easily addressed by FPV.
  Once that is augmented by register update tracking (to translate from TL ops to reg values).
  That can then check that the state of the two status interrupts tracks the level appropriately.
  It can also check that each interrupt is only asserted to the processor when enabled by `INTR_ENABLE`.
  The behaviour is also stimulated by the `interrupts` UVM testpoint.

  Addressed by:
  - (---) (**FPV**)
  - `interrupts` (**UVM**)

- **3.10**: `CURR_FIFO_LVL` gives the current WR and RD levels.

  As with the related interrupts, this can be addressed by FPV.
  It is also checked by occasional register reads in `sw_op`.

  Addressed by:
  - (---) (**FPV**)
  - `sw_op` (**UVM**)

- **3.11**: `FIFO_CLR` clears the write and read FIFOs individually (by writing 1 to the corresponding field).

  This can by addressed by FPV, where it's essentially a handshake between the register top and the HW.
  The properties should check that writing 1 to one field clears only the corresponding FIFO.

  Addressed by:
  - (---) (**FPV**)

- **3.12**: `STATUS` fields and reset value 0xA.

  Addressed by:
  - `smoke` (**UVM**)
  - `sw_op` (**UVM**)
  - `seed_read` (**UVM**)
  - `csr_hw_reset` (**UVM**)

- **3.13**: An operation started when RRAM is not accessible (before init/key load, or after RMA entry) is rejected with `ERR_CODE.op_err`.

  There are several different reasons that RRAM might not be accessible.
  As such, addressing all of these properly will be easiest with FPV.
  There is also a UVM testpoint (`rma_sw_dis`) which shows it happen explicitly.

  Addressed by:
  - (---) (**FPV**)
  - `rma_sw_dis` (**UVM**)

- **3.14**: FIFO pointers use duplicate counters (`FIFO.CTR.REDUN`).

  Addressed by a fault injection test (which changes one of the counters and checks for a fatal alert).

  Addressed by:
  - `sec_cm_fifo_ctr_redun` (**SEC**)

- **3.15**: Starting a write clears the write FIFO.

  This can be addressed by FPV (checking that when a write starts, the FIFO level is set to zero).
  The requirement also states that any previously pushed data will be discarded.
  This is shown for a FIFO if the first item out of the FIFO after a clear is the first one pushed in.

  Addressed by:
  - (---) (**FPV**)

- **3.16**: FIFO flow control during an operation (stall on full read FIFO / empty write FIFO).

  The claim about 32-bit words in the read FIFO is shown for any operation that reads through the FIFO.
  Since there are no length or valid signals, the whole 32 bits must be pushed and we see the result match.
  The different speeds of consuming the read FIFO in `sw_op` checks the stalling behaviour.
  Similarly, the testpoint writes to the write FIFO with different rates.
  This will test the stall/resume behaviour there.

  Addressed by:
  - `sw_op` (**UVM**)

- **3.17**: A multi-word operation aborts at the first error and `ERR_ADDR` records its address.

  Addressed by:
  - `memory_protection` (**UVM**)
  - `otp_region_protection` (**UVM**)
  - `emul_info_window` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

- **3.18**: On a multi-word read error, the full number of words is returned, all-ones from the failing word onwards.

  Addressed by:
  - `memory_protection` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

## 4. Memory protection

- **4.1**: There are `NumRegions` data-partition MP regions, disabled at reset.

  See each region match, crossed with the allowed operations and configuration.
  The minimum and maximum possible sizes for a matching region should be seen.
  We should see regions that fall off the top of the partition.

  Addressed by:
  - `mp_region_cg` (**CG**)
  - `smoke` (**UVM**)
  - `memory_protection` (**UVM**)
  - `csr_hw_reset` (**UVM**)

- **4.2**: A disabled region is not matched.

  Addressed by:
  - `mp_disabled_region_cg` (**CG**)
  - `memory_protection` (**UVM**)

- **4.3**: `DEFAULT_REGION` applies when no region matches, and denies all access at reset.

  Addressed by:
  - `mp_region_cg` (**CG**)
  - `memory_protection` (**UVM**)
  - `csr_hw_reset` (**UVM**)

- **4.4**: Per-page info partition protection with `INFO_PAGE_CFG_n`, disabled at reset.

  Addressed by:
  - `info_page_cg` (**CG**)
  - `csr_hw_reset` (**UVM**)
  - `smoke` (**UVM**)
  - `memory_protection` (**UVM**)
  - `seed_partition` (**UVM**)
  - `isolated_partition` (**UVM**)

- **4.5**: Data and info region configurations are locked with REGWEN registers.

  This covers the countermeasures `DATA_REGIONS.CONFIG.REGWEN` and `INFO_PAGE.CONFIG.REGWEN`.

  Since there are lots of regwen registers, this is most amenable to FPV.
  For each regwen, that will test the `rw0c` behaviour and the way it controls access to the appropriate region/page.
  For an extra layer of certainty, full transactions are seen by the `regwen_csr_and_corresponding_lockable_csr` testpoint.

  Addressed by:
  - (---) (**FPV**)
  - `regwen_csr_and_corresponding_lockable_csr` (**UVM**)

- **4.6**: There are two windows that define emulated info page regions.

  As with 4.5, this is most amenable to FPV but uses `regwen_csr_and_corresponding_lockable_csr` for extra certainty.

  Addressed by:
  - (---) (**FPV**)
  - `regwen_csr_and_corresponding_lockable_csr` (**UVM**)

- **4.7**: Window `EN` bits: deny gaps, block `host_tl`, fail closed on overlap, deny entry independent of REGWEN.

  This will be easiest to prove with FPV but the current plan has two UVM tests as a backup.

  Addressed by:
  - (---) (**FPV**)
  - `emul_info_window` (**UVM**)
  - `emul_info_window_overlap` (**UVM**)

- **4.8**: Emulated subregions

  The number of subregions gives a large configuration space, which is easiest to address by FPV.
  For extra confidence, this is also checked with a UVM testpoint.

  Addressed by:
  - (---) (**FPV**)
  - `emul_info_subregion` (**UVM**)

- **4.9**: Conditions for a subregion to be active.

  This is definitely most easy to check with FPV.
  There are also two UVM testpoints that sample the space of configurations.

  Addressed by:
  - (---) (**FPV**)
  - `emul_info_subregion` (**UVM**)
  - `emul_info_window_overlap` (**UVM**)

- **4.10**: Subregion permissions in `EMUL_INFO_SUBREGION_CFG_n`, with an optional separate lock.

  As with 4.5, the regwen behaviour is most amenable to checking with FPV.
  The permission behaviour is sampled with a UVM testpoint.

  Addressed by:
  - (---) (**FPV**)
  - `emul_info_permissions` (**UVM**)

- **4.11**: Overriding permissions for info pages

  This combination of configuration bits is most amenable to checking with FPV.

  Addressed by:
  - (---) (**FPV**)

- **4.12**: Info-partition access is gated by `lc_ctrl` enables, ANDed with `INFO_PAGE_CFG_n`.

  This can be addressed by FPV, but there are also related UVM testpoints defined.

  Addressed by:
  - (---) (**FPV**)
  - `seed_partition` (**UVM**)
  - `isolated_partition` (**UVM**)

- **4.13**: A permission violation in a SW-initiated transaction sets `ERR_CODE.mp_err` and latches `ERR_ADDR`.

  Addressed by:
  - `smoke` (**UVM**)
  - `memory_protection` (**UVM**)
  - `otp_region_protection` (**UVM**)
  - `seed_partition` (**UVM**)
  - `isolated_partition` (**UVM**)
  - `emul_info_window` (**UVM**)
  - `emul_info_permissions` (**UVM**)

- **4.14**: Four controller-path requesters (`SwSel`, `HwOtpSel`, `HwLcMgrSel`, `HwLoopBack`).

  This requirement is more of a description of the shape of the block.
  It makes sense to check that each requester exists, but these are checked by other requirements:
  - `SwSel`: Requirements 2.1 and 2.2.
  - `HwOtpSel`: Requirement 6.1.
  - `HwLcMgrSel`: Requirement 7a.3.
  - `HwLoopBack`: Requirement 5.9.

- **4.15**: Priority order for software data-partition accesses (OTP exclusion, subregions, window deny, MP regions, default).

  The layers in this requirement are most easily addressed by FPV.
  There are also related UVM testpoints.

  Addressed by:
  - (---) (**FPV**)
  - `otp_region_protection` (**UVM**)
  - `emul_info_window` (**UVM**)
  - `emul_info_window_overlap` (**UVM**)

- **4.16**: Hardware requesters bypass software-configured protection.

  This is easiest to address with FPV (because the resulting properties don't have to mention the things that don't matter).
  The behaviour is also stimulated by UVM testpoints.

  Addressed by:
  - (---) (**FPV**)
  - `smoke` (**UVM**)
  - `rewrite_op` (**UVM**)
  - `rma` (**UVM**)

- **4.17**: OTP hardware plug protection: OTP pages only, fixed attributes.

  This is easiest to address with FPV.
  The behaviour is also stimulated by a UVM testpoint.

  Addressed by:
  - (---) (**FPV**)
  - `otp_standalone` (**UVM**)

- **4.18**: LCMGR hardware plug protection is phase-dependent (`PhaseSeed`, `PhaseRma`).

  Showing the precise times when lcmgr accesses are allowed is easiest with FPV.
  There are also UVM testpoints that do accesses in times when they are allowed.

  Addressed by:
  - (---) (**FPV**)
  - `seed_read` (**UVM**)
  - `rma` (**UVM**)

- **4.19**: `addr_xor_en` is hardwired, not software-configurable.

  The associated testpoints use backdoor accesses to see whether XOR infection is enabled.
  This way, they can check that it is enabled at the right time.

  Addressed by:
  - `smoke` (**UVM**)
  - `otp_standalone` (**UVM**)
  - `sec_cm_mem_addr_infection` (**SEC**)

## 5. Scrambling, address infection and ECC

- **5.1**: Optional per-region XEX/PRINCE scrambling (`SCRAMBLE_EN`).

  This covers the countermeasure `MEM.SCRAMBLE`.

  This is only visible with backdoor access (because the keys can't be changed without reset).
  As such, it's easiest to check with UVM tests.
  Seeing the queue for access to the scrambler is tracked in `scrambler_queue_cg`.

  Addressed by:
  - `scrambler_queue_cg` (**CG**)
  - `smoke` (**UVM**)
  - `memory_protection` (**UVM**)
  - `emul_info_permissions` (**UVM**)
  - `sec_cm_mem_scramble` (**SEC**)

- **5.2**: Scrambling keys are sideloaded from OTP and not readable by SW.

  This covers the countermeasure `SCRAMBLE.KEY_SIDELOAD`.

  Addressed by:
  - `smoke` (**UVM**)
  - `sec_cm_scramble_key_sideload` (**SEC**)

- **5.3**: Address-XOR infection on write, removed on read; disabled for OTP accesses.

  Addressed by:
  - `smoke` (**UVM**)
  - `host_read_direct` (**UVM**)
  - `otp_standalone` (**UVM**)
  - `sec_cm_mem_addr_infection` (**SEC**)

- **5.4**: ECC is done by the macro, controlled by `ecc_en` from the region config.

  The attached UVM testpoints stimulate ECC through the macro.
  Any FPV test will check that the `ECC_EN` field for regions and info page gets reported correctly.

  Addressed by:
  - (---) (**FPV**)
  - `ecc_cg` (**CG**)
  - `memory_protection` (**UVM**)
  - `emul_info_permissions` (**UVM**)
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

- **5.5**: Correctable ECC counters (`CORR1_ERR_CNT`, `CORR2_ERR_CNT`) and interrupts.

  This covers the countermeasure `MEM.INTEGRITY`.

  Addressed by:
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)
  - `otp_macro_ecc_err` (**UVM**)

- **5.6**: The counters are 8 bits wide, can be read and written by SW, and saturate.

  Addressed by:
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)

- **5.7**: `CORR1_ERR_LOC`/`CORR2_ERR_LOC` hold the last corrected address and partition.

  Addressed by:
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)
  - `otp_macro_ecc_err` (**UVM**)

- **5.8**: Uncorrectable ECC error sets `FAULT_STATUS.phy_relbl_err` and raises `fatal_err`.

  Addressed by:
  - `op_after_uncorr_cg` (**CG**)
  - `ecc_uncorr_err` (**UVM**)
  - `local_esc_relbl_err` (**UVM**)
  - `otp_macro_ecc_err` (**UVM**)

- **5.9**: `Rewrite` reads and writes back one corrected RRAM word.

  Addressed by:
  - `rewrite_op` (**UVM**)
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)

- **5.10**: Read-set-write capability used for emulated OTP semantics.

  Addressed by:
  - `otp_standalone` (**UVM**)
  - `otp_write_blank_err` (**UVM**)

- **5.11**: Corrected errors don't abort operations.

  Addressed by:
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)

- **5.12**: A corrected error is reported once per RRAM read (not again by the shadow read).

  Addressed by:
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)

- **5.13**: XEX construction with two interleaved PRINCE instances and `cipher_switch`.

  Addressed by:
  - `smoke` (**UVM**)
  - `sec_cm_mem_scramble` (**SEC**)
  - `sec_cm_mem_readback` (**SEC**)

- **5.14**: Scrambling key management (netlist constants before `keys_valid`, random keys after disable).

  There are UVM tests that check the main path, where keys from OTP are used.
  We will use FPV to check behaviour of accesses before providing the key, which use netlist constants.
  Similarly, it will check behaviour after RMA (which either uses the netlist constants or random keys).

  Addressed by:
  - (---) (**FPV**)
  - `smoke` (**UVM**)
  - `sec_cm_scramble_key_sideload` (**SEC**)

- **5.15**: Write data path ordering, with zero-fill and `wr_intg_err` on bus-integrity failure.

  This covers the countermeasure `MEM.BUS.INTEGRITY`.
  The behaviour on wdata integrity failure is easiest to verify with FPV.

  Addressed by:
  - (---) (**FPV**)
  - `tl_intg_err_cg` (**CG**)
  - `tl_errors_cg`  (**CG**)
  - `smoke` (**UVM**)
  - `sw_op` (**UVM**)
  - `sec_cm_mem_bus_integrity` (**SEC**)

- **5.16**: Read data path integrity computation.

  The ECC decoding and integrity computation are addressed by any test that reads RRAM.
  The claim that the address XOR is kept in the read buffer needs inspection of internal signals and will be done with FPV.

  Addressed by:
  - (---) (**FPV**)
  - `smoke` (**UVM**)
  - `host_read_direct` (**UVM**)

## 6. Emulated OTP (`rram_ctrl_otp`)

- **6.1**: The `otp_macro_i` and `otp_macro_o` ports have the interface expected by `otp_ctrl`.

  Adherence to the protocol can be checked most easily with FPV.
  Correctness of address decoding is guaranteed by any UVM test with an OTP access.
  The supported sizes are tracked (in more detail) in requirement 6.2.
  Note that there is no checking required for 48 bit requests: behaviour for that size is not specified.

  Addressed by:
  - (---) (**FPV**)
  - `otp_standalone` (**UVM**)

- **6.2**: OTP command set

  Addressed by:
  - `otp_cmd_cg` (**CG**)
  - `otp_standalone` (**UVM**)

- **6.3**: OTP bits can only be set; clearing gives `MacroWriteBlankError`.

  Addressed by:
  - `otp_standalone` (**UVM**)
  - `otp_write_blank_err` (**UVM**)

- **6.4**: Hamming (72,64) OTP integrity page.

  This covers the countermeasure `OTP.MEM.INTEGRITY`.

  Addressed by:
  - `otp_standalone` (**UVM**)
  - `otp_intg_err` (**UVM**)
  - `sec_cm_otp_mem_integrity` (**SEC**)

- **6.5**: Integrity checking and update per OTP command.

  This covers the countermeasure `MEM.READBACK`.

  Addressed by:
  - `otp_standalone` (**UVM**)
  - `otp_intg_err` (**UVM**)
  - `sec_cm_mem_readback` (**SEC**)

- **6.6**: Response signals `fatal_lc_fsm_err`, `fatal_alert` and `recov_alert` on `otp_macro_o`.

  These signals are always zero, which is tracked by a simple FPV check.

  Addressed by:
  - (---) (**FPV**)

- **6.7**: OTP error reporting in `FAULT_STATUS` and `STD_FAULT_STATUS`.

  The mapping from OTP errors to the two registers can be tracked with FPV.
  For an extra layer, errors that are seen in UVM tests are also tracked in covergroups.

  Addressed by:
  - (---) (**FPV**)
  - `fault_status_err_cg` (**CG**)
  - `std_fault_status_err_cg` (**CG**)
  - `otp_macro_ecc_err` (**UVM**)
  - `sec_cm_ctr_redun` (**SEC**)
  - `sec_cm_mem_bus_integrity` (**SEC**)

- **6.8**: The OTP region doesn't use scrambling or address infection.

  This is tracked in the scoreboard for any OTP access.

  Addressed by:
  - `otp_standalone` (**UVM**)
  - `otp_region_protection` (**UVM**)

- **6.9**: `rram_ctrl_otp` FSM is sparse and its counters are redundant.

  Addressed by:
  - `sec_cm_fsm_sparse` (**SEC**)
  - `sec_cm_ctr_redun` (**SEC**)

- **6.10**: OTP clock domain crossing.

  Synchronisation between the OTP and main clocks is tested by running the two at different frequencies.
  This requirement is then addressed by any test that accesses OTP.

  Addressed by:
  - `otp_standalone` (**UVM**)

- **6.11**: Macro ECC on the OTP path: correctable errors are invisible, uncorrectable errors give `MacroError`.

  Addressed by:
  - `otp_macro_ecc_err` (**UVM**)

- **6.12**: OTP bus integrity on read words; integrity added to written words.

  Addressed by:
  - `sec_cm_mem_bus_integrity` (**SEC**)

## 7. Life cycle, key manager and power manager interactions

### 7a. Initialisation and seeds

- **7a.1**: `INIT.VAL` requests keys and reads seeds before allowing other use.

  The UVM test checks that the correct keys are used.
  FPV is used to check that accesses before initialisation are blocked.

  Addressed by:
  - (---) (**FPV**)
  - `seed_read` (**UVM**)

- **7a.2**: Initialisation status reporting (`STATUS.init_done`, `STATUS.keys_valid`, `PHY_STATUS.init_done`).

  Addressed by:
  - `smoke` (**UVM**)
  - `seed_read` (**UVM**)

- **7a.3**: Seeds read twice, compared, and forwarded to `keymgr_dpe` with `seed_valid`.

  FPV is used to check that `seed_valid` bits are cleared when the controller is disabled.

  Addressed by:
  - (---) (**FPV**)
  - `seed_read` (**UVM**)
  - `seed_read_err` (**UVM**)

- **7a.4**: `lc_seed_hw_rd_en` gates the HW seed read.

  Addressed by:
  - `seed_cg` (**CG**)
  - `seed_read` (**UVM**)

- **7a.5**: Phy initialisation precedes all accesses.

  The `init_done` signal being asserted can be seen from the smoke UVM test.
  The requirement that `rram_phy` doesn't send any macro requests earlier than that can be checked with FPV.

  Addressed by:
  - (---) (**FPV**)
  - `smoke` (**UVM**)

- **7a.6**: Seed integrity checking in `rram_ctrl_lcmgr`.

  Addressed by:
  - `seed_read_err` (**UVM**)

- **7a.7**: RMA request during initialisation skips the rest of init; RMA entry after initialisation reseeds the LFSR from `rma_seed`.

  Addressed by:
  - `rma` (**UVM**)

### 7b. Life cycle controller

- **7b.1**: `lc_escalate_en` disables all RRAM accesses.

  This property can be checked by FPV.

  Addressed by:
  - (---) (**FPV**)

- **7b.2**: `lc_tx` signals use MuBi-style encodings.

  This covers the countermeasure `LC_CTRL.INTERSIG.MUBI`.

  An FPV test will check that all values other than `On` are treated as `Off`.
  It will also check that the `rma_acq` output is always a valid MuBi.

  Addressed by:
  - (---) (**FPV**)

### 7c. RMA secure wipe

- **7c.1**: Response to `rma_req`

  This covers the countermeasure `RMA_ENTRY.MEM.SEC_WIPE`.

  Addressed by:
  - `rma_cg` (**CG**)
  - `rma` (**UVM**)
  - `sec_cm_rma_entry_mem_sec_wipe` (**SEC**)

- **7c.2**: After RMA, SW access is disabled until reset; OTP and lcmgr interfaces are unaffected.

  Addressed by:
  - `rma` (**UVM**)
  - `rma_sw_dis` (**UVM**)

- **7c.3**: SW access is disabled from the start of RMA entry.

  Addressed by:
  - `rma_sw_dis` (**UVM**)

- **7c.4**: RMA-phase counters are redundant.

  Addressed by:
  - `sec_cm_ctr_redun` (**SEC**)

- **7c.5**: LCMGR errors are reported in `FAULT_STATUS` and `STD_FAULT_STATUS`.

  Addressed by:
  - `fault_status_err_cg` (**CG**)
  - `std_fault_status_err_cg` (**CG**)
  - `seed_read_err` (**UVM**)
  - `sec_cm_ctr_redun` (**SEC**)

- **7c.6**: RMA waits for an in-progress software operation.

  Addressed by:
  - `rma` (**UVM**)
  - `rma_sw_dis` (**UVM**)

- **7c.7**: Wipe and verify procedure with running XOR digests.

  Addressed by:
  - `rma` (**UVM**)
  - `sec_cm_rma_entry_mem_sec_wipe` (**SEC**)

- **7c.8**: RMA failure leaves the FSM in `StInvalid`, disables the controller and withholds `rma_ack`.

  Addressed by:
  - (---) (**FPV**)

- **7c.9**: Registers remain accessible after RMA.

  Addressed by:
  - `rma` (**UVM**)

### 7d. Power manager

- **7d.1**: Idle reporting to `pwrmgr`.

  Addressed by:
  - (---) (**FPV**)

- **7d.2**: `PHY_STATUS.wr_busy` indicates the phy is writing.

  Addressed by:
  - (---) (**FPV**)

## 8. RRAM phy behaviour

- **8.1**: The phy bridges 32-bit bus words to the 128-bit macro word and arbitrates host vs controller.

  Addressed by:
  - `smoke` (**UVM**)
  - `host_controller_arb` (**UVM**)

- **8.2**: The 4-entry read buffer, invalidated on writes to the same page.

  Addressed by:
  - `rd_buf_cg` (**CG**)
  - `host_read_direct` (**UVM**)
  - `rd_buf_eviction` (**UVM**)

- **8.3**: Shadow reads, with a mismatch raising `FAULT_STATUS.phy_rd_intg_err`.

  Addressed by:
  - `sec_cm_mem_readback` (**SEC**)
  - `sec_cm_phy_rd_buf_ctrl_integrity` (**SEC**)

- **8.4**: Up to 2 outstanding host reads

  Addressed by:
  - `host_read_direct` (**UVM**)

- **8.5**: Phy consistency checks (host grant, origin metadata, `spurious_done`).

  Addressed by:
  - `sec_cm_phy_host_grant_ctrl_consistency` (**SEC**)
  - `sec_cm_phy_rsp_ctrl_consistency` (**SEC**)

- **8.6**: Read path control flow checks (`phy_rd_ctrl_err`).

  Addressed by:
  - `sec_cm_phy_rd_rsp_ctrl_integrity` (**SEC**)
  - `sec_cm_phy_rsp_ctrl_consistency` (**SEC**)

- **8.7**: Duplicated phy arbiters, sparse `rram_phy_wr` FSM, redundant counters.

  Addressed by:
  - `sec_cm_fsm_sparse` (**SEC**)
  - `sec_cm_phy_arbiter_ctrl_redun` (**SEC**)
  - `sec_cm_ctr_redun` (**SEC**)

- **8.8**: Phy arbitration suppression rules.

  Tracking the arbitration is easiest with FPV.

  Addressed by:
  - (---) (**FPV**)
  - `host_controller_arb` (**UVM**)
  - `hw_sw_arb` (**UVM**)
  - `rma_cg` (**CG**)

- **8.9**: Read pipeline latency and buffer states.

  Addressed by:
  - `host_read_direct` (**UVM**)

- **8.10**: Multi-page writes are split into per-page macro writes.

  Addressed by:
  - `sw_op` (**UVM**)

## 9. RRAM macro interface

- **9.1**: Macro request signals.

  Because these are signals *from* `rram_ctrl` there is no need to track coverage for correctness.
  Track that every signal is used in order to make sure that `rram_ctrl` is using the whole interface.

  Addressed by:
  - `macro_req_cg` (**CG**)
  - `smoke` (**UVM**)
  - `sw_op` (**UVM**)

- **9.2**: Macro response signals.

  Addressed by:
  - `macro_rsp_cg` (**CG**)
  - `smoke` (**UVM**)
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

- **9.3**: `ecc_err` one-hot0 encoding.

  Addressed by:
  - `macro_rsp_cg` (**CG**)
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

- **9.4**: Macro handshake (stable until `ack`, one `ack` per request).

  Correctness of the macro handshake can be checked with FPV

  Addressed by:
  - (---) (**FPV**)

- **9.5**: Macro write sequence (push words, commit with `wr_last`).

  Addressed by:
  - `sw_op` (**UVM**)

## 10. Interrupts

- **10.1**: Seven interrupts (`wr_empty`, `wr_lvl`, `rd_full`, `rd_lvl`, `op_done`, `corr1_err`, `corr2_err`).

  Addressed by:
  - `interrupts_cg` (**CG**)
  - `interrupts` (**UVM**)
  - `intr_test` (**UVM**)
  - `ecc_corr1_err` (**UVM**)
  - `ecc_corr2_err` (**UVM**)

- **10.2**: `INTR_STATE` reset is 0x3.

  Addressed by:
  - `csr_hw_reset` (**UVM**)

- **10.3**: Level interrupts `wr_lvl` and `rd_lvl`.

  Addressed by:
  - `interrupts` (**UVM**)

- **10.4**: `INTR_ENABLE`/`INTR_TEST` follow the standard pattern.

  Addressed by:
  - `intr_test` (**UVM**)

## 11. Alerts, error and fault reporting

- **11.1**: Five alerts and `ALERT_TEST`.

  Addressed by:
  - `alert_test` (**UVM**)

- **11.2**: `recov_err` fires when a SW operation completes with any `ERR_CODE` bit set.

  Addressed by:
  - `memory_protection` (**UVM**)
  - `emul_info_window` (**UVM**)
  - `error_invalid_op` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

- **11.3**: `fatal_std_err` fires when any `STD_FAULT_STATUS` bit is set.

  There are several UVM tests that trigger this.
  The properly can be checked by FPV.

  Addressed by:
  - (---) (**FPV**)
  - `tl_intg_err` (**UVM**)
  - `seed_read_err` (**UVM**)
  - `sec_cm_reg_bus_integrity` (**SEC**)
  - `sec_cm_ctr_redun` (**SEC**)
  - `sec_cm_fifo_ctr_redun` (**SEC**)
  - `sec_cm_phy_arbiter_ctrl_redun` (**SEC**)

- **11.4**: `fatal_err` fires when any `FAULT_STATUS` bit is set.

  There are several UVM tests that trigger this.
  The properly can be checked by FPV.

  Addressed by:
  - (---) (**FPV**)
  - `ecc_uncorr_err` (**UVM**)
  - `local_esc_relbl_err` (**UVM**)
  - `otp_macro_ecc_err` (**UVM**)
  - `seed_read_err` (**UVM**)
  - `sec_cm_mem_readback` (**SEC**)
  - `sec_cm_phy_host_grant_ctrl_consistency` (**SEC**)
  - `sec_cm_phy_rsp_ctrl_consistency` (**SEC**)
  - `sec_cm_phy_rd_rsp_ctrl_integrity` (**SEC**)

- **11.5**: Macro error alerts `fatal_macro_err` and `recov_macro_err`.

  The fact that these alerts are triggered by the macro errors can be checked by FPV.

  Addressed by:
  - (---) (**FPV**)

- **11.6**: `ERR_CODE` (all `rw1c`, all recoverable): `op_err`, `mp_err`, `rd_err`, `wr_err`.

  The tests must check that the appropriate field of `ERR_ADDR` is set for a failing operation.
  They must also check that the fields of `ERR_CODE` can be cleared.
  The covergroup tracks the operation that was run, crossed with the error flags.
  The combination checks that each of the ways to set fields in `ERR_ADDR` is seen.

  Addressed by:
  - `sw_err_cg` (**CG**)
  - `memory_protection` (**UVM**)
  - `error_invalid_op` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)
  - `write_intg_err` (**UVM**)

- **11.7**: `phy_relbl_err` is clearable but clearing it doesn't undo escalation.

  Addressed by:
  - `ecc_uncorr_err` (**UVM**)
  - `local_esc_relbl_err` (**UVM**)

- **11.8**: `FAULT_STATUS` bit list.

  Addressed by:
  - `ecc_uncorr_err` (**UVM**)
  - `otp_macro_ecc_err` (**UVM**)
  - `seed_read_err` (**UVM**)
  - `sec_cm_mem_readback` (**SEC**)
  - `sec_cm_phy_host_grant_ctrl_consistency` (**SEC**)
  - `sec_cm_phy_rsp_ctrl_consistency` (**SEC**)
  - `sec_cm_phy_rd_rsp_ctrl_integrity` (**SEC**)

- **11.9**: An integrity-caused `rd_err`/`wr_err` also sets the matching fault bit.

  Addressed by:
  - `sec_cm_mem_bus_integrity` (**SEC**)

## 12. Disable, execute and escalation controls

- **12.1**: `DIS.SW_DIS` disables RRAM until reset.

  This covers the countermeasure `MEM_DISABLE.CONFIG.MUBI`.

  This can be checked easily by FPV.

  Addressed by:
  - (---) (**FPV**)
  - `sec_cm_mem_disable_config_mubi` (**SEC**)

- **12.2**: `DIS.LOCAL_ESC_RELBL_ERR` makes `phy_relbl_err` disable the RRAM.

  This can be checked easily by FPV.

  Addressed by:
  - (---) (**FPV**)
  - `local_esc_relbl_err` (**UVM**)
  - `ecc_uncorr_err` (**UVM**)

- **12.3**: `EXEC.EN` magic value controls instruction fetches from RRAM (data reads are not affected).

  This covers the countermeasure `EXEC.CONFIG.REDUN`.

  This can be checked easily by FPV.
  The properties should check that instruction fetches through `host_tl` are blocked unless `EXEC.EN` holds the magic value.
  They should also check that data reads through `host_tl` are unaffected by the value of `EXEC.EN`.

  Addressed by:
  - (---) (**FPV**)
  - `sec_cm_exec_config_redun` (**SEC**)

- **12.4**: Global escalation makes memory inaccessible.

  This covers the countermeasure `MEM.CTRL.GLOBAL_ESC`.

  This can be checked easily by FPV.

  Addressed by:
  - (---) (**FPV**)

- **12.5**: Local escalation on a subset of fatal errors, latched until reset.

  This covers the countermeasure `MEM.CTRL.LOCAL_ESC`.

  This can be checked easily by FPV.

  Addressed by:
  - (---) (**FPV**)
  - `sec_cm_mem_ctrl_local_esc` (**SEC**)
  - `local_esc_relbl_err` (**UVM**)
  - `seed_read_err` (**UVM**)

- **12.6**: Effect of disable (requests blocked, OTP macro disabled, random keys, `seed_valid` cleared, registers accessible).

  This can be checked easily by FPV.

  Addressed by:
  - (---) (**FPV**)
  - `sec_cm_mem_ctrl_local_esc` (**SEC**)
  - `sec_cm_mem_disable_config_mubi` (**SEC**)
  - `local_esc_relbl_err` (**UVM**)

## 13. Security countermeasures

- **13.1** (Bus integrity): `REG.BUS.INTEGRITY`, `HOST.BUS.INTEGRITY`, `MEM.BUS.INTEGRITY` (**UVM**)

  The `REG.BUS.INTEGRITY` countermeasure is covered by requirement 2.8.
  The `HOST.BUS.INTEGRITY` countermeasure is covered by requirement 2.8.
  The `MEM.BUS.INTEGRITY` countermeasure is covered by requirement 5.15.

- **13.2** (Data protection): `MEM.ADDR_INFECTION`, `MEM.SCRAMBLE`, `SCRAMBLE.KEY.SIDELOAD`, `MEM.INTEGRITY`, `OTP.MEM.INTEGRITY`, `MEM.READBACK` (**UVM**)

  The `MEM.ADDR_INFECTION` countermeasure is covered by requirement 2.6.
  The `MEM.SCRAMBLE` countermeasure is covered by requirement 5.1.
  The `SCRAMBLE.KEY_SIDELOAD` countermeasure is covered by requirement 5.2.
  The `MEM.INTEGRITY` countermeasure is covered by requirement 5.5.
  The `OTP.MEM.INTEGRITY` countermeasure is covered by requirement 6.4.
  The `MEM.READBACK` countermeasure is covered by requirement 6.5.

- **13.3** (Config locking): `CTRL.CONFIG.REGWEN`, `DATA_REGIONS.CONFIG.REGWEN`, `INFO_PAGE.CONFIG.REGWEN` (**UVM**)

  The `CTRL.CONFIG.REGWEN` countermeasure is covered by requirement 3.6.
  The `DATA_REGIONS.CONFIG.REGWEN` countermeasure is covered by requirement 4.5.
  The `INFO_PAGE.CONFIG.REGWEN` countermeasure is covered by requirement 4.5.

- **13.4** (Disable and escalation): `MEM.CTRL.GLOBAL_ESC`, `MEM.CTRL.LOCAL_ESC`, `MEM_DISABLE.CONFIG.MUBI`, `EXEC.CONFIG.REDUN`, `LC_CTRL.INTERSIG.MUBI` (**UVM**)

  The `MEM.CTRL.GLOBAL_ESC` countermeasure is covered by requirement 12.4.
  The `MEM.CTRL.LOCAL_ESC` countermeasure is covered by requirement 12.5.
  The `MEM_DISABLE.CONFIG.MUBI` countermeasure is covered by requirement 12.1.
  The `EXEC.CONFIG.REDUN` countermeasure is covered by requirement 12.3.
  The `LC_CTRL.INTERSIG.MUBI` countermeasure is covered by requirement 7b.2.

- **13.5** (Secure wipe): `RMA_ENTRY.MEM.SEC_WIPE` (**UVM**)

  This `RMA_ENTRY.MEM.SEC_WIPE` countermeasure is covered by requirement 7c.1.

- **13.6** (Sparse FSMs): `CTRL.FSM.SPARSE`, `PHY_WR.FSM.SPARSE`, `HOST_TL_LC_GATE.FSM.SPARSE`, `WR_TL_LC_GATE.FSM.SPARSE` (**UVM**)

  Fault injection to check sparse FSMs is not covered by any other requirement.

  Addressed by:
  - `sec_cm_fsm_sparse` (**SEC**)

- **13.7** (Redundant counters, arbiters and FIFOs): `CTR.REDUN`, `FIFO.CTR.REDUN`, `PHY_ARBITER.CTRL.REDUN` (**UVM**)

  Fault injection to check redundant counters is not covered by any other requirement.

  Addressed by:
  - `sec_cm_ctr_redun` (**SEC**)
  - `sec_cm_fifo_ctr_redun` (**SEC**)
  - `sec_cm_phy_arbiter_ctrl_redun` (**SEC**)

- **13.8** (Consistency checks): `PHY_HOST_GRANT.CTRL.CONSISTENCY`, `PHY_RSP.CTRL.CONSISTENCY`, `PHY_RD_RSP.CTRL.INTEGRITY`, `PHY_RD_BUF.CTRL.INTEGRITY` (**UVM**)

  Fault injection to check these consistency checks is not covered by another requirement.

  Addressed by:
  - `sec_cm_phy_host_grant_ctrl_consistency` (**SEC**)
  - `sec_cm_phy_rsp_ctrl_consistency` (**SEC**)
  - `sec_cm_phy_rd_rsp_ctrl_integrity` (**SEC**)
  - `sec_cm_phy_rd_buf_ctrl_integrity` (**SEC**)

## 14. Register-level conventions

- **14.1**: Collisions where HW and SW write a register on the same cycle

  Checking the arbitration across the different registers will be easiest with FPV.

  Addressed by:
  - (---) (**FPV**)

- **14.2**: MuBi4 encoding for enable/disable fields

  Addressed by:
  - `csr_hw_reset` (**UVM**)
  - `memory_protection` (**UVM**)
  - `emul_info_permissions` (**UVM**)
  - `sec_cm_mem_disable_config_mubi` (**SEC**)

- **14.3**: Software-writable REGWENs are `rw0c`, reset 1, one-way.

  Addressed by:
  - `csr_rw` (**UVM**)
  - `regwen_csr_and_corresponding_lockable_csr` (**UVM**)

- **14.4**: `DIS` fields, `INIT.VAL` and similar are `rw1s`.

  Addressed by:
  - `csr_rw` (**UVM**)
  - `csr_bit_bash` (**UVM**)

- **14.5**: Register access and reset values

  Addressed by:
  - `csr_hw_reset` (**UVM**)
  - `csr_mem_rw_with_rand_reset` (**UVM**)
  - `csr_aliasing` (**UVM**)

- **14.6**: Register bus integrity is checked and sets `STD_FAULT_STATUS.reg_intg_err`.

  Addressed by:
  - `tl_intg_err` (**UVM**)
  - `sec_cm_reg_bus_integrity` (**SEC**)

- **14.7**: The `SCRATCH` register has no hardware function but is accessible by software.

  The automated CSR tests check that the register can be written and read back, with the expected reset value.

  Addressed by:
  - `csr_hw_reset` (**UVM**)
  - `csr_rw` (**UVM**)
  - `csr_bit_bash` (**UVM**)
