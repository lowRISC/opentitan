# rram_ctrl requirements document

This document is extracted from the specification across five files:
- The [top-level `rram_ctrl` documentation](../README.md) (**T**)
- The feature list in [rram_ctrl.hjson](../data/rram_ctrl.hjson) (**F**)
- The [register description](../doc/registers.md) (**R**)
- The [interface description](../doc/interfaces.md) (**I**)
- The [programmer's guide](../doc/programmers_guide.md) (**P**)
- The [theory of operation](../doc/theory_of_operation.md) (**O**)
- The documentation for [reggen](../../../../util/reggen/README.md) (**G**)
The bold letters after those files are used as source references in the requirements below.

Some of these requirements vary with parameters (like keys, memory sizes and FIFO depths).
However, the `SecScrambleEn` parameter is assumed to be true.
To support a version of `rram_ctrl` with `SecScrambleEn=0`, this document would need to be generalised.

From specification documents, the requirements can be broken into the following set of buckets:
1. Memory organisation and address map
2. Bus interfaces (TL-UL)
3. Software operation interface (CONTROL / ADDR / FIFOs)
4. Memory protection (data regions, info pages, emulated info windows)
5. Scrambling, address infection and ECC
6. Emulated OTP (`rram_ctrl_otp`)
7. Life cycle, key manager and power manager interactions (incl. RMA wipe and init)
8. RRAM phy (`rram_phy`) behaviour
9. RRAM macro interface
10. Interrupts
11. Alerts, error and fault reporting
12. Disable / execute / escalation controls
13. Security countermeasures
14. Register-level conventions (REGWEN, reset values, MuBi encoding)

## 1. Memory organisation and address map

- **1.1**: The RRAM has two separately-addressed partitions: **data** and **info**.

  Each partition's address range starts at 0.
  SW selects between them with `CONTROL.PARTITION` (0 for data, 1 for info).

  Source for requirement: T Address Map, R CONTROL, P

- **1.2**: The first `NumDataPages - NumOtpPages` pages of the data partition contain general-purpose data.

  They are accessible by host, SW and lcmgr-hw-if.

  Source for requirement: T

- **1.3**: Page `NumDataPages - NumOtpPages` of the data partition holds OTP integrity words.

  It is accessible only by otp-hw-if.

  Source for requirement: T

- **1.4**: The last `NumOtpPages-1` pages of the data partition hold OTP data.

  They are accessible only by otp-hw-if.
  Together with the integrity page, the top 6 pages (3 KiB) of the data partition form the OTP region.
  The OTP region is inaccessible to software:
  - Software-initiated controller operations to it fail with a memory protection error (`ERR_CODE.mp_err`).
  - Host reads to it return a TL-UL error.
  - The RMA wipe does not touch it.

  Source for requirement: T, P, O

- **1.5**: Info partition: `NumInfoPages` pages, accessible by SW and lcmgr-hw-if only (never the host).

  Page 5 is `CreatorInfoPage` (`0xA00`)
  Page 6 is `OwnerInfoPage` (`0xC00`)
  Page 7 is `IsolatedInfoPage` (`0xE00`)

  Source for requirement: T, P, F (`INFO.CREATOR_PARTITION`, `INFO.ISOLATED_PARTITION`, `INFO.OWNER_PARTITION`)

- **1.6**: There are `NumEmulInfoRegions` windows with emulated info pages on the data partition.

  Each has up to 12 independently lockable subregions.
  They provide info-page-like storage beyond the `NumInfoPages` physical info pages.
  Access through `host_tl` is always blocked.

  Source for requirement: T Features, R `EMUL_INFO_*`, P, O

- **1.7**: Address granularity

  The RRAM address space is byte-addressed.

  Source for requirement: T Address Map

## 2. Bus interfaces (TL-UL)

- **2.1**: `core_tl` is a TL-UL device interface.

  It carries register access, FIFO windows and SW-initiated transactions.
  It can reach the data and info partitions.

  Source for requirement: T, I

- **2.2**: `host_tl` is a TL-UL device interface that is **read-only** and limited to the data partition.

  It is used for instruction fetch and direct data reads.
  It cannot reach the info partition or the OTP region.

  Source for requirement: T, I, P, F (`OP.HOST_READ`)

- **2.3**: Two separate access windows exist for the FIFOs.

  The bus gets back-pressure when the write FIFO is full or the read FIFO is empty.
  The FIFOs have depth `WrFifoDepth` and `RdFifoDepth`, respectively.

  Source for requirement: R intro

- **2.4**: `wr_fifo` is write-only; `rd_fifo` is read-only.

  Both are single-word windows, and byte writes are not supported.

  Source for requirement: R

- **2.5**: `wr_fifo` may only be programmed after a write operation has been initiated via `CONTROL`.

  A write to `wr_fifo` while no software operation is in progress completes normally, without a TL-UL error response.
  The data is discarded and does not reach the FIFO.

  If RRAM access is disabled (see section 12), writes to `wr_fifo` return a TL-UL error.

  Source for requirement: T, R wr_fifo, P Issuing a Controller Write

- **2.6**: Host reads return the data with integrity added in `rram_phy_rd`.

  The integrity is passed through `u_tl_adapter_host`.
  The address infection is removed in `u_tl_adapter_host`.

  Source for requirement: I HOST.BUS.INTEGRITY, MEM.ADDR_INFECTION, O

- **2.7**: TL-UL gating primitives (`HOST_TL_LC_GATE`, `WR_TL_LC_GATE`) have sparse FSMs.

  Source for requirement: I

- **2.8**: Command integrity on both TL-UL interfaces

  Both `core_tl` and `host_tl` check the command integrity of every request.
  A failing check returns an error response and is a fatal fault.
  A `core_tl` register access with failing integrity asserts `fatal_std_err` immediately.
  A `host_tl` request with invalid command integrity is not forwarded to the RRAM.
  It sets `STD_FAULT_STATUS.reg_intg_err`, which asserts `fatal_std_err` and triggers local escalation.

  Source for requirement: T Features, O Transmission Integrity Faults, F (`ESCALATION`)

- **2.9**: Host reads are subject to memory protection

  `host_tl` reads are checked against the same software-configured MP regions and `DEFAULT_REGION` as the controller path.
  The check uses a dedicated region-select instance in `rram_ctrl_mp` (`host_sel_cfg`/`host_mp_err`), independent of the controller-path requesters.

  Source for requirement: P Memory-Mapped Reads via `host_tl`, O Requesters

- **2.10**: Host read error responses

  Correctable ECC errors on a host read are fixed transparently.
  They raise `corr1_err`/`corr2_err` and record the location in `CORR1_ERR_LOC`/`CORR2_ERR_LOC` (see 5.5).
  Uncorrectable ECC errors or integrity failures on a host read produce an in-band TL-UL error response.

  Source for requirement: P Error Encountered by Host Direct Read

## 3. Software operation interface (CONTROL / ADDR / FIFOs)

- **3.1**: Supported ops are `Read` (0), `Write` (1) and `Rewrite` (2).

  Other values are reserved and give `ERR_CODE.op_err`.

  Source for requirement: R CONTROL.OP, ERR_CODE, P

- **3.2**: `CONTROL.NUM` (10 bits) is the number of bus words minus 1.

  The maximum is 1024 bus words per transaction (`CtrlMaxWords`).
  `NUM` is ignored for a `Rewrite` (see 5.9).

  Source for requirement: T, R, P, O RRAM Write Data Path

- **3.3**: Writing 1 to `CONTROL.START`, starts an RRAM transaction.

  The transaction is specified by `ADDR` and the other fields of `CONTROL` (`NUM`, `PARTITION`, `OP`).

  Source for requirement: R

- **3.4**: Write / Rewrite operation size and alignment

  RRAM words are 128b / 16B / 4 bus words long.
  A valid Write or Rewrite operation must have a base address that is a multiple of this value.
  A valid Write operation must also have a length that is a multiple of four bus words.
  This length is `CONTROL.NUM+1`, so a valid Write operation has `CONTROL.NUM == 3 mod 4`.

  If the base address or length aren't appropriately aligned, the operation will not affect RRAM.
  The `OP_STATUS.err` and `ERR_CODE.op_err` fields will be set when the operation completes.

  Source for requirement: T, R ADDR.START, R NUM, P Write Alignment

- **3.5**: `ADDR.START` is a 21-bit byte address within the selected partition.

  Reads truncate to a bus-word (4 B) aligned address: for example, `0x13` becomes `0x10`.

  Source for requirement: R ADDR.START, P

- **3.6**: `CTRL_REGWEN.EN` is HW-controlled.

  It clears when an operation starts and re-sets when the operation completes, whether the operation succeeded or failed.
  While it is 0, `CONTROL` and `ADDR` cannot be changed.

  Source for requirement: R CTRL_REGWEN

- **3.7**: `OP_STATUS.done` and `.err` are set by HW and cleared by SW.

  Error details are in `ERR_CODE`.

  Source for requirement: R OP_STATUS

- **3.8**: `INTR_STATE.op_done` signals operation completion.

  On completion of a Read, Write or Rewrite, the controller sets `OP_STATUS.done` and asserts the `op_done` interrupt.

  Source for requirement: I, P

- **3.9**: `FIFO_LVL.WR` and `FIFO_LVL.RD` set the interrupt watermarks.

  These control the `wr_lvl` and `rd_lvl` status interrupts.
  The state for the `wr_lvl` interrupt is set if the write FIFO has at most `FIFO_LVL.WR` items.
  The state for the `rd_lvl` interrupt is set if the read FIFO has at least `FIFO_LVL.RD` items.
  In both cases, the interrupt is only asserted to the processor if `INTR_ENABLE` is true.

  Source for requirement: R FIFO_LVL, P FIFO Management

- **3.10**: `CURR_FIFO_LVL` gives the current WR and RD levels (RO).

  Source for requirement: R, P

- **3.11**: `FIFO_CLR` (WO) clears the write and read FIFOs individually.

  Writing 1 to a field will clear the corresponding FIFO.

  Source for requirement: R, P

- **3.12**: `STATUS` reports `rd_full`, `rd_empty`, `wr_full`, `wr_empty`, `init_done` and `keys_valid`.

  Reset value is 0xA (`rd_empty` and `wr_empty` set).

  Source for requirement: R STATUS

- **3.13**: An operation started when RRAM is not accessible sets `ERR_CODE.op_err`.

  This happens before init and key load have completed (both `lcmgr_init_done` and `lcmgr_keys_valid`), or when SW access is disabled from RMA entry.
  Such an operation is rejected by the arbiter: it is not started, but completes immediately with `OP_STATUS.err` and `ERR_CODE.op_err` set.

  Source for requirement: R ERR_CODE, P Initialization, O Stage 2, O RMA Handling

- **3.14**: FIFO pointers are implemented with duplicate counters (`FIFO.CTR.REDUN`).

  Source for requirement: I

- **3.15**: Starting a write clears the write FIFO

  Setting `CONTROL.START` for a write operation clears the write FIFO, discarding any data pushed to it earlier.
  Write data must be pushed after the start.

  Source for requirement: P Issuing a Controller Write

- **3.16**: FIFO flow control during an operation

  During a read, the controller pushes 32-bit bus words into the read FIFO.
  It stalls when the read FIFO is full and resumes when space is available.
  During a write, the controller drains the write FIFO.
  It stalls when the write FIFO is empty and resumes when data is available.

  Source for requirement: P Issuing a Controller Read, P Issuing a Controller Write

- **3.17**: Errors during multi-word controller operations

  A multi-word operation aborts at the first error.
  `ERR_ADDR` records the address at which the first error was encountered.

  Source for requirement: P Error Encountered by Software Initiated Controller Operations

- **3.18**: Errors during multi-word controller reads

  On the first error during a multi-word read, the controller enters an error state (`StErr`) and stops issuing RRAM read requests.
  It still returns the full requested number of words to the read FIFO, so software does not deadlock.
  Starting with the word where the error occurred, every returned word is all-ones (`0xFFFFFFFF`) with valid bus integrity.
  No further RRAM accesses are made, and no data from other concurrent operations appears in the read FIFO.

  Source for requirement: P Errors During Multi-Word Controller Reads

## 4. Memory protection

- **4.1**: There are `NumRegions` data-partition MP regions.

  The layout of a region is defined by its `MP_REGION_n` register (which gives the base page and region size).
  `SIZE` is one less than the number of pages: the region covers pages `[BASE, BASE + SIZE]` inclusive.
  The region configuration is defined by `MP_REGION_CFG_n`.
  That configuration controls whether the region is enabled, whether it can be read/written, whether it is scrambled and whether to use ECC.
  On reset, all regions are disabled (`EN = MuBi4False`).

  Source for requirement: T, R, P Configuring Memory Protection, F (`MEM_PROTECTION`)

- **4.2**: A region that is disabled (`EN != MuBi4True`) is not matched against transactions.

  Source for requirement: R, P

- **4.3**: `DEFAULT_REGION` configures access when no region rule matches.

  It has no `EN` and no REGWEN.
  On reset it denies all access (`RD_EN`, `WR_EN`, `SCRAMBLE_EN` and `ECC_EN` are all `MuBi4False`).

  Source for requirement: T, R, P

- **4.4**: The info partition has per-page protection.

  This is configured with eight `INFO_PAGE_CFG_n` registers (`EN`, `RD_EN`, `WR_EN`, `SCRAMBLE_EN`, `ECC_EN`).
  If the `EN` field is not `MuBi4True` then the info page is disabled and all accesses to it are denied.
  The field is `MuBi4False` at reset: a page is only accessible after software has programmed its `INFO_PAGE_CFG_n`.

  Source for requirement: T, R, P

- **4.5**: Data and info region configurations are locked with REGWEN registers.

  Each data region has its own `REGION_CFG_REGWEN_n` (`NumRegions` registers).
  If it is not set then the corresponding `MP_REGION_CFG_n` and `MP_REGION_n` registers are locked.

  Each info page has its own `INFO_REGWEN_n` (`NumInfoPages` registers).
  If this is not set then the corresponding `INFO_PAGE_CFG_n` is locked.

  These REGWENs are separate (clearing the write enable for one region doesn't affect access to other regions).
  All are `rw0c`: once cleared to 0, they stay locked until reset.

  Source for requirement: I, R, P

- **4.6**: There are two windows that define emulated info page regions.

  These are defined by registers `EMUL_INFO_REGION_n` (`NumEmulInfoRegions` registers).
  These registers contain `BASE`, `SIZE` and `EN` fields.
  An emulated info region is lockable with `EMUL_INFO_REGWEN_n`.
  The hardware does not constrain where a window is placed within the data partition.

  Source for requirement: R, O Emulated Info Pages, F (`MEM_PROTECTION.EMULATED_INFO_PAGES`)

- **4.7**: Enable bits for emulated info page regions.

  When `EN` is set in the region's `EMUL_INFO_REGION_n` register, any access not covered by an enabled subregion is denied by a window-wide deny entry.
  When `EN` is not set, neither the window nor its subregions are matched.
  Access through `host_tl` is always blocked.
  If two enabled windows overlap, the subregions of both windows are disabled and both deny entries stay active, so both windows are denied entirely.
  This holds regardless of which window was configured and locked first.

  The deny entry depends only on the multi-bit `EN` field, not on `EMUL_INFO_REGWEN`.
  So a fault that flips the regwen back to 1 disables the subregions but keeps the whole window denied.

  Source for requirement: R `EMUL_INFO_REGION`, P, O

- **4.8**: Emulated subregions

  There are `NumEmulInfoSubregions` emulated info subregions in the data partition.
  These are defined by registers `EMUL_INFO_SUBREGION_n`
  Each register consists of an 8-bit `TOP` field, which uses top-of-range addressing relative to the window base.
  Subregion 0 of a window covers offsets `[0, TOP_0]`, and each later subregion runs from the previous TOP+1 to its own TOP.
  Subregions must be configured in strictly increasing TOP order and locked from the first subregion of the window.

  Source for requirement: R `EMUL_INFO_SUBREGION`, P, O, F (`MEM_PROTECTION.EMULATED_INFO_PAGES`)

- **4.9**: A subregion is active only if all of the following hold.

  1. Its window is enabled and locked via `EMUL_INFO_REGWEN`.
  1. The placement of this and every lower-indexed subregion in the window is locked via `EMUL_INFO_SUBREGION_REGWEN`.
  1. TOP does not exceed the window SIZE.
  1. The window does not overlap another enabled window.

  Source for requirement: R, P, O

- **4.10**: Subregion permissions are in `EMUL_INFO_SUBREGION_CFG_n`

  These registers have a separate lock (`EMUL_INFO_SUBREGION_CFG_REGWEN_n`) from placement.
  Locking the permissions is optional.
  A subregion becomes accessible once its placement is locked, whether or not its permissions are also locked.

  Source for requirement: R, P, O

- **4.11**: Overriding permissions for info pages

  If `SCRAMBLE_DIS` is `MuBi4True` then scrambling is disabled when lcmgr addresses an info page.
  If it is `MuBi4False` then scrambling matches the hardwired hardware info configure rules.

  Similarly, ECC is disabled for that info page if `ECC_DIS` is `MuBi4True`.
  If it is `MuBi4False` then ECC enablement matches the hardwired hardware info configure rules.

  By default the hardware assumes scrambling and ECC are enabled on the seed pages when it reads them.
  If the seed pages were provisioned without scrambling or ECC, `HW_INFO_CFG_OVERRIDE` must be set to match.

  Source for requirement: R, P Errors Encountered During Hardware Initiated Operations

- **4.12**: Info-partition access is gated by `lc_ctrl`

  Software access to the special info pages is gated by signals from `lc_ctrl`.
  Each access is only possible while the corresponding enable is `On`:
  - `lc_creator_seed_sw_rw_en`: software read and write of the creator seed page.
  - `lc_owner_seed_sw_rw_en`: software read and write of the owner seed page.
  - `lc_iso_part_sw_rd_en`: software read of the isolated page.
  - `lc_iso_part_sw_wr_en`: software write of the isolated page.

  Each enable is ANDed with the page's software-configured `RD_EN`/`WR_EN`.
  So life cycle can only further restrict access, never grant it beyond what `INFO_PAGE_CFG_n` allows.

  Source for requirement: T System Interactions, I, P, O Memory Protection for LCMGR Hardware Plug

- **4.13**: A permission violation in a SW-initiated transaction sets `ERR_CODE.mp_err` and latches `ERR_ADDR`.

  An access that does not satisfy `rd_en` or `wr_en` for the requested operation is blocked and the transaction is rejected (`ctrl_mp_err`).

  Source for requirement: R, P, O Access attributes

- **4.14**: Controller-path requesters

  There are four controller-path requesters, each with its own protection rules:
  - `SwSel`: software (core TL-UL)
  - `HwOtpSel`: OTP hardware interface (`rram_ctrl_otp`)
  - `HwLcMgrSel`: life cycle manager (`rram_ctrl_lcmgr`)
  - `HwLoopBack`: internal loopback, used for the `Rewrite` operation

  Source for requirement: O Requesters

- **4.15**: Priority order for software data-partition accesses

  Software accesses are matched against a single priority-ordered list, highest first:
  1. A fixed OTP exclusion region (`SwInitDataCfg`, region index 0), which denies all reads and writes to the OTP page range.
     It is not exposed via any register and cannot be reconfigured or overridden.
  1. The emulated info subregions.
  1. The per-window deny entries.
  1. The configurable MP regions, lowest-indexed match first.

  If nothing matches, `DEFAULT_REGION` applies.
  As a consequence, a subregion can never grant access to the OTP region, and a gap in a window never falls through to the MP regions or the default region.

  Source for requirement: O Data partition, O Emulated Info Pages, O Memory Protection for OTP Hardware Plug

- **4.16**: Hardware requesters bypass software-configured protection

  OTP and lcmgr accesses ignore the software-configured regions.
  They are matched instead against fixed compile-time tables.

  Source for requirement: O Data partition

- **4.17**: OTP hardware plug protection

  `HwOtpSel` accesses are matched against `HwOtpDataCfg`, which grants `rd_en` and `wr_en` for the OTP region pages only.
  All other addresses are rejected.
  OTP region accesses use fixed attributes: `scramble_en = MuBi4False`, `ecc_en = MuBi4True`, `addr_xor_en = MuBi4False`.

  Source for requirement: O Memory Protection for OTP Hardware Plug

- **4.18**: LCMGR hardware plug protection is phase-dependent

  Each lcmgr rule is tagged with a `phase`, and access is granted only when the lcmgr FSM's current phase matches:
  - `PhaseSeed`: creator and owner info pages read-only, no data partition access.
  - `PhaseRma`: creator, owner and isolated info pages read-write, all non-OTP data pages read-write.

  Source for requirement: O Information partition, O Memory Protection for LCMGR Hardware Plug

- **4.19**: `addr_xor_en` is not software-configurable

  It is hardwired to `MuBi4True` for the software-configurable data regions and info pages.
  It has a fixed value per hardware-access table otherwise (e.g. `MuBi4False` for the OTP region).

  Source for requirement: O Access attributes

## 5. Scrambling, address infection and ECC

- **5.1**: XEX scrambling with PRINCE, optional and set per region or info page (`SCRAMBLE_EN`).

  This is shared between read and write paths in `rram_scramble`.
  Requests from the two paths are queued and served in order.
  Pages with `scramble_en = MuBi4False` are stored unscrambled.

  Source for requirement: T, O RRAM Scrambling

- **5.2**: Scrambling keys are sideloaded from emulated OTP via `otp_ctrl` and `rram_ctrl_otp` (`otp_key`).

  SW cannot read them.

  Source for requirement: T, I

- **5.3**: Address-XOR (infection)

  Each bus word is XORed with its bus-word address on write in `rram_phy_wr` and un-XORed on read.
  Reads un-XOR in `u_tl_adapter_host` (host) or `u_rram_ctrl_rd` (controller).
  The stored XORed value stays intact through the read pipeline and read buffer, and is only removed at the output stage.
  Address-XOR infection is disabled for OTP-partition accesses.

  Source for requirement: T, I, O Address-XOR

- **5.4**: ECC uses the macro's own error detection and correction.

  This is signalled through the `ecc_en` signal that is passed to the macro.
  That signal will match the `ECC_EN` field in the region or info page configuration.

  Source for requirement: T, I, O

- **5.5**: Correctable ECC counters

  Single-bit corrections raise `corr1_err` and increment `CORR1_ERR_CNT`.
  Double-bit corrections raise `corr2_err` and increment `CORR2_ERR_CNT`.

  Source for requirement: T, R, P, O

- **5.6**: The counters are 8 bits wide and saturate (do not wrap).

  They can both be read and written by SW.

  Source for requirement: R

- **5.7**: `CORR1_ERR_LOC` and `CORR2_ERR_LOC` hold the last corrected address (21b) and partition.

  Source for requirement: R, P

- **5.8**: Uncorrectable ECC error handling.

  An uncorrectable macro ECC (`ecc_err[2] = 1`) is fatal and sets `FAULT_STATUS.phy_relbl_err`.
  The `fatal_err` alert is always raised.
  RRAM access is only disabled by it if `DIS.LOCAL_ESC_RELBL_ERR` is set (see 12.2).

  Source for requirement: T, R, O Multi-Bit Error

- **5.9**: `CONTROL.OP = Rewrite` reads one RRAM word and writes the corrected word back.

  Software can issue a `Rewrite` at any time.
  `NUM` is ignored: the hardware always reads and writes back exactly one full RRAM word (4 bus words, 16 bytes).
  The data is not exposed to software or to the read/write FIFOs.
  A rewrite is only supported on pages with ECC enabled (`ECC_EN` set in the matching `MP_REGION_CFG`, `DEFAULT_REGION`, `EMUL_INFO_SUBREGION_CFG` or `INFO_PAGE_CFG`).
  On completion it sets `OP_STATUS.done` and asserts `op_done`.
  If the internal read or write fails, `OP_STATUS.err` is set and the failure is reported through `ERR_CODE`/`ERR_ADDR` as for a normal read or write.

  Source for requirement: T, R, P Issuing a Rewrite Operation

- **5.10**: The controller includes a read-set-write capability on the RRAM, used for emulated OTP semantics.

  Source for requirement: T

- **5.11**: Corrected errors don't abort operations

  A corrected (single- or double-bit) error does not abort the in-progress operation, and the corrected data is returned normally.

  Source for requirement: P Correctable ECC Errors, O RRAM ECC Error Handling

- **5.12**: Correctable error reporting frequency

  A corrected error is reported once per RRAM read of the affected word.
  The shadow read of the same word does not report it a second time.
  The same word is reported again if it is read from the RRAM again later (for example, after it was evicted from the read buffer).

  Source for requirement: O RRAM ECC Error Handling

- **5.13**: XEX construction

  The tweak is `addr_tweak = GF_MULT(word_addr, addr_key)`.
  Encryption is `ciphertext = PRINCE(addr_tweak XOR plaintext, data_key) XOR addr_tweak`.
  Decryption is `plaintext = PRINCE^-1(addr_tweak XOR ciphertext, data_key) XOR addr_tweak`.
  The 128-bit word is processed by two interleaved 64-bit PRINCE instances using the same key.
  On the shadow-read verify pass, `cipher_switch` swaps which instance processes the even-indexed and odd-indexed data bits.

  Source for requirement: O RRAM Scrambling, O RRAM Read Integrity

- **5.14**: Scrambling key management

  Before `keys_valid` is asserted, the scrambler uses fixed netlist constants (`RndCnstAddrKey`, `RndCnstDataKey`).
  Once `keys_valid` is asserted, the sideloaded keys are latched in.
  If RRAM access is later disabled, the scrambler switches to a pair of random keys (`rand_addr_key`, `rand_data_key`), also supplied by `otp_ctrl` in the scrambling-key response.

  Source for requirement: O Scrambling key management, O RRAM Escalation & Disable

- **5.15**: Write data path ordering

  For each RRAM word written:
  1. Each of the four bus words is checked for bus-transmission integrity.
     A word that fails the check is zero-filled (the write is not aborted).
  1. Each bus word is XORed with its bus-word address.
  1. The four words are packed into one 128-bit RRAM word.
  1. The word is scrambled (if enabled).
  1. The macro computes the ECC and the word is written.

  A write-data integrity mismatch also asserts `wr_intg_err`, which is a fatal fault.

  Source for requirement: O Write Data Path, O Transmission Integrity Faults

- **5.16**: Read data path integrity computation

  On a read miss, the word is read, ECC-decoded by the macro, descrambled and split into four bus words.
  The 7-bit bus integrity of each word is computed for the data with the address XOR removed.
  The stored word (in the read buffer) keeps the address XOR.

  Source for requirement: O Read Data Path

## 6. Emulated OTP (`rram_ctrl_otp`)

- **6.1**: The `otp_macro_i` and `otp_macro_o` ports have the interface expected by `otp_ctrl`.

  This is a ready/valid command interface, sending responses in order (with no back-pressure from `otp_ctrl`).
  Addresses on the interface count 16-bit words.
  Supported sizes: 16/32/64 bits (not 48 bits: that size is not supported by `rram_ctrl`).

- **6.2**: The command set is `OtpRead`, `OtpWrite`, `OtpReadRaw`, `OtpWriteRaw`, `OtpInit` and `OtpZeroize`.

  - `OtpRead`: Read OTP word and verify Hamming integrity
  - `OtpWrite`: Write OTP word (RSW: bits can only be set) and update integrity word
  - `OtpReadRaw`: Read OTP data bypassing integrity check
  - `OtpWriteRaw`: Write OTP data bypassing integrity check
  - `OtpZeroize`: Zeroize OTP word (writing all ones); update integrity word; read back word written
  - `OtpInit`: Initialize the OTP partition

  The first five commands each operate on a single OTP word, which is 16, 32 or 64 bits wide.

  Source for requirement: T, P Accessing the OTP Region, O OTP Hardware Plug

- **6.3**: OTP semantics: bits can only be set, never cleared.

  This is implemented with a read-set-write algorithm on the reserved OTP partition.
  Both `OtpWrite` and `OtpWriteRaw` enforce it.
  A write that attempts to clear a bit that is already set returns `MacroWriteBlankError`.

  Source for requirement: T, O

- **6.4**: OTP integrity: an 8-bit Hamming (72,64) value per 64 bits of OTP data is stored in a separate integrity page.

  This is in addition to the macro ECC.
  The syndrome is stored at the offset in the integrity page that corresponds to the data's position.
  The code is plain and non-inverting: all-zero data encodes to an all-zero syndrome, and all-ones data encodes to an all-ones syndrome.
  So an erased, unprogrammed word already carries a valid syndrome, and the integrity page needs no initialisation before first use.

  Source for requirement: T, I, O Integrity Scheme

- **6.5**: Integrity checking and update per command

  - `OtpRead` reads the integrity word, reads the data word, recomputes the integrity and compares.
    A mismatch returns `MacroEccUncorrError`.
  - `OtpWrite` and `OtpZeroize` update the integrity word after the data word is written.
    `OtpWrite` updates both the data word and the integrity word in one operation.
  - After an `OtpWrite` or `OtpWriteRaw`, the written data word is read back and its recomputed ECC is compared against the ECC captured at write time.
    A mismatch returns `MacroEccUncorrError`.
  - `OtpZeroize` reads the written word back and returns it to `otp_ctrl`.
  - `OtpReadRaw` and `OtpWriteRaw` bypass the integrity page.

  Source for requirement: T, O Integrity Scheme

- **6.6**: Response signals `fatal_lc_fsm_err`, `fatal_alert` and `recov_alert` are provided by `otp_macro_o`.

  Source for requirement: T struct

- **6.7**: OTP error reporting

  OTP-path errors are reported in the fields of `FAULT_STATUS`:
  - `otp_op_err`: undefined operation issued
  - `otp_mp_err`: memory protection violation
  - `otp_rd_err`: RRAM read error (ECC or integrity failure)
  - `otp_wr_err`: RRAM write error

  FSM or count errors go to `STD_FAULT_STATUS.otp_err`.
  Transmission-integrity errors on the OTP interface set `STD_FAULT_STATUS.otp_intg_err`.

  Source for requirement: R, P Errors on the OTP Interface

- **6.8**: The OTP region doesn't use scrambling or address infection.

  Source for requirement: T, P, O OTP Hardware Plug

- **6.9**: `rram_ctrl_otp` FSM is sparse-encoded and its counters are redundantly encoded.

  Source for requirement: I

- **6.10**: OTP clock domain

  The `otp_macro_i`/`otp_macro_o` and `otp_key_o`/`otp_key_i` interfaces are synchronous to `clk_otp_i`/`rst_otp_ni`.
  Everything else in `rram_ctrl` is synchronous to `clk_i`.
  `rram_ctrl_otp` crosses the clock domains with an asynchronous FIFO (`prim_fifo_async`) in each direction.
  `rram_ctrl_lcmgr` crosses the key request with a req/ack synchronizer (`prim_sync_reqack`).

  Source for requirement: T System Interactions, I, O

- **6.11**: Macro ECC on the OTP path

  Correctable errors on OTP-path reads are corrected transparently and never surface as an error.
  Uncorrectable errors return `MacroError` to `otp_ctrl` and set `FAULT_STATUS.otp_rd_err` or `FAULT_STATUS.otp_wr_err`, which raises `fatal_err`.

  Source for requirement: O Integrity Scheme

- **6.12**: OTP bus integrity

  `rram_ctrl_otp` checks the bus integrity of each read word from the RRAM read pipeline.
  On a failure, a sticky `data_invalid` flag is latched (until reset) and `intg_err_o` is asserted, causing a fatal fault.
  A word with failing integrity that is being accumulated into the internal word register (`rram_word_q`) is poisoned to all-ones.
  `rram_ctrl_otp` adds bus integrity to every word it writes to the RRAM.

  Source for requirement: O Transmission Integrity Faults

## 7. Life cycle, key manager and power manager interactions

### 7a. Initialisation and seeds

- **7a.1**: `INIT.VAL` (`rw1s`) initialises the controller.

  The controller requests the address and data scramble keys, and reads the root seeds from RRAM, before allowing other use.
  `keys_valid` is asserted after both keys are acknowledged.

  Source for requirement: R INIT, P, O Stage 2, F (`INIT.SCRAMBLING_KEYS`, `INIT.ROOT_SEEDS`)

- **7a.2**: Initialisation status reporting.

  `STATUS.init_done` and `STATUS.keys_valid` report init progress.
  `PHY_STATUS.init_done` reports phy and RRAM init.

  Source for requirement: R, P, O

- **7a.3**: Seeds read during initialisation

  During init, the creator and owner seeds are read from their info pages and forwarded to `keymgr_dpe` (`keymgr_creator_seed`, `keymgr_owner_seed`), each with a `seed_valid` bit.
  Each seed (256 bits, read as 8 bus words) is read twice.
  The words from the second pass are compared with those from the first, and a discrepancy sets `FAULT_STATUS.seed_err`.
  Other unexpected failures also set `FAULT_STATUS.seed_err`.
  A seed is only marked valid if both reads completed without a read error, an integrity error or a discrepancy.
  The `seed_valid` bits are cleared when the controller is disabled.

  Source for requirement: T, R, P, O Stage 2

- **7a.4**: `lc_seed_hw_rd_en` gates whether the HW seed is read.

  If it is not set (device not provisioned), the seeds are not read and remain invalid, and init completes after the keys are loaded.

  Source for requirement: I, T, P, O

- **7a.5**: Phy initialisation precedes all accesses

  After reset, the macro self-initialises and asserts `init_done`, which `rram_phy` latches into `phy_init_done` (`PHY_STATUS.init_done`).
  Until then, `rram_phy` issues no requests to the macro and the arbiter stays in reset, so no RRAM access is possible (including hardware interfaces).

  Source for requirement: T rram_macro_rsp_t, P Auto-initialization, O Stage 1

- **7a.6**: Seed integrity checking

  The bus integrity of each seed word is checked in `rram_ctrl_lcmgr`.
  A failure latches `data_invalid` until the next reset, so a corrupt seed is never used.

  Source for requirement: O Transmission Integrity Faults

- **7a.7**: RMA request during initialisation

  If `rma_req` arrives while the lcmgr FSM is idle or requesting keys, the FSM skips the rest of initialisation and starts the RMA wipe.
  After initialisation, the FSM waits for an RMA request.
  On RMA entry after initialisation, the LFSR is reseeded from `rma_seed` before wiping begins.

  Source for requirement: O Stage 2

### 7b. Life cycle controller

- **7b.1**: `lc_escalate_en` is an escalation input.

  It disables all RRAM accesses (global escalation).

  Source for requirement: I, T, F (`ESCALATION`)

- **7b.2**: `lc_tx` signals are MuBi-style `lc_tx` encodings (`LC_CTRL.INTERSIG.MUBI`).

  This applies to signals connecting to `lc_ctrl`.
  The inputs in the list are:
  - `lc_creator_seed_sw_rw_en`
  - `lc_owner_seed_sw_rw_en`
  - `lc_iso_part_sw_rd_en`
  - `lc_iso_part_sw_wr_en`
  - `lc_seed_hw_rd_en`
  - `lc_escalate_en`
  - `rma_req`
  In each case, the important value is `On`.
  As such, the expected property is that any other value is treated the same as `Off`.

  The only output signal sent to `lc_ctrl` is `rma_ack`.
  This is also a MuBi and will always have a valid encoding.

  Source for requirement: I

### 7c. RMA secure wipe

- **7c.1**: Response to `rma_req`

  On `rma_req` from `lc_ctrl`, the `rram_ctrl_lcmgr` FSM overwrites the following pages (table `RmaWipeEntries`):
  + creator seed page (info page 5)
  + owner seed page (info page 6)
  + isolated info page (info page 7)
  + all data partition pages below the OTP region

  Other info pages and the OTP region are not wiped.
  It uses pseudo-random data from a 64-bit LFSR, seeded by `rma_seed` if RMA is requested after initialisation.
  Once the RMA wipe is complete, the FSM asserts `rma_ack`.

  Source for requirement: T, I, O RMA Handling, F (`RMA`)

- **7c.2**: Once RMA completes, software RRAM access is disabled until the next reset.

  After a successful wipe, the lcmgr FSM stays in `StRmaRsp` until reset, drives `rma_ack` and keeps `rma_sw_dis_o = On`.
  The RRAM itself is not disabled: the OTP and lcmgr hardware interfaces are unaffected, so `lc_ctrl` can still program the new life cycle state through OTP.

  Source for requirement: T, O RMA Handling, F (`RMA`)

- **7c.3**: SW access is disabled from the start of RMA entry.

  From the start of RMA entry (`StEntropyReseed` or `StRmaWipe`), `rma_sw_dis_o` is asserted:
  - New software operations are rejected and completed immediately with `OP_STATUS.err` and `ERR_CODE.op_err`.
  - Host reads, including instruction fetches, are answered with an error.

  Software can still reach the OTP pages through `otp_ctrl`'s direct access interface.

  Source for requirement: R, O RMA Handling, F (`RMA`)

- **7c.4**: Word count, page count and wipe index in the RMA phase use redundant counters.

  Source for requirement: I CTR.REDUN

- **7c.5**: LCMGR errors are reported in `FAULT_STATUS` and `STD_FAULT_STATUS`.

  The `FAULT_STATUS` fields are:
  - `lcmgr_op_err`: undefined operation issued
  - `lcmgr_mp_err`: memory protection violation
  - `lcmgr_rd_err`: RRAM read error (ECC or integrity failure)
  - `lcmgr_wr_err`: RRAM write error

  FSM or count errors set `STD_FAULT_STATUS.lcmgr_err`, and transmission-integrity errors set `STD_FAULT_STATUS.lcmgr_intg_err`.

  Source for requirement: R, P Errors Encountered During Hardware Initiated Operations

- **7c.6**: RMA waits for an in-progress software operation

  On RMA entry, the controller waits for any pending RRAM transaction to complete before switching priority to the hardware interface.
  A software operation already in progress when RMA entry starts completes normally, including its FIFO window accesses.
  The wipe starts only once the arbiter has returned to idle.
  An operation that never completes (e.g. a write for which software never provides all words) blocks the RMA entry.

  Source for requirement: O RMA Handling

- **7c.7**: Wipe and verify procedure

  For each wipe entry, the inner FSM writes LFSR data to every word of each page and then reads each word back.
  It accumulates a running XOR digest of the written words and of the words read back.
  Once a page has been read back, the two digests are compared and a mismatch is an error.

  Source for requirement: O RMA Handling

- **7c.8**: RMA failure

  If any wipe or verify step fails, the lcmgr FSM enters `StInvalid`.
  It continuously asserts `rma_dis_access_o = On` and keeps `rma_ack` deasserted.
  The controller is disabled completely (see 12.6) and `lc_ctrl` does not complete the RMA transition.

  Source for requirement: O RMA Handling

- **7c.9**: Registers remain accessible after RMA

  After both successful and failed RMA entry, the `rram_ctrl` registers can still be accessed.

  Source for requirement: O RMA Handling

### 7d. Power manager

- **7d.1**: Idle reporting

  `rram_ctrl` asserts only idle to `pwrmgr` when it is safe to power down (no write or OTP operation in progress).

  Source for requirement: T, I

- **7d.2**: `PHY_STATUS.wr_busy` indicates the phy is writing.

  Source for requirement: R

## 8. RRAM phy behaviour

- **8.1**: The phy bridges 32-bit bus words to the 128-bit macro word.

  It arbitrates between the read-only host TL-UL and the muxed controller interface.

  Source for requirement: T, O RRAM Phy

- **8.2**: The phy read buffer

  The read buffer has 4 entries of 128 bits, acting as a small read-only cache.
  Each entry stores four bus words with their 7-bit bus integrity (4 × 39 bits).
  Entries are invalidated on any write to the same RRAM page in the same partition.
  The read buffer has no software-visible configuration.

  Source for requirement: T, O RRAM Read Buffer

- **8.3**: Shadow reads

  Every RRAM read is issued twice (shadow read).
  The first result is returned to the requester; the second is compared in the background when the RRAM is idle.
  The shadow read uses the same address and pipeline configuration (`addr`, `part`, `descramble_en`, `ecc_en`, `addr_xor_en`) as the first read.
  A mismatch invalidates the buffer entry and raises a fatal alert (`FAULT_STATUS.phy_rd_intg_err`).

  Source for requirement: T, I, O RRAM Read Integrity, O RRAM Read Buffer

- **8.4**: Up to 2 outstanding host read requests are tracked in the read pipeline (`NumOutstandingRdReq`).

  Source for requirement: T, O RRAM Phy

- **8.5**: Phy consistency checks

  Phy checks: the host grant is consistency-checked (never granted with info-partition access, never granted with no request).
  The host/controller origin of each accepted read is stored redundantly in the metadata FIFO and checked on readout.
  An unexpected `done` or an origin mismatch raises an error (`spurious_done`).

  Source for requirement: I, R, O RRAM Phy

- **8.6**: Read path control flow checks

  Control-flow errors in the read path set `phy_rd_ctrl_err`.
  Possible control flow errors are:
  - `data_valid` with an empty meta FIFO
  - `data_valid` while a verify completes
  - an RRAM request with no internal request
  - response integrity not matching the request in the meta FIFO

  Source for requirement: I, R

- **8.7**: Arbiter consistency checks

  The phy arbiters (controller/host arbiter and shared scramble arbiter) are duplicated and compared continuously.
  The `rram_phy_wr` FSM is sparse and its counters are redundant.

  Source for requirement: I

- **8.8**: Phy arbitration suppression

  The host is suppressed while any of the following hold:
  - a controller write is pending or a write is in progress
  - the host interface is disabled
  - phy initialisation is not complete

  The controller is suppressed while any of the following hold:
  - a controller read or write is already in flight
  - a write is in progress
  - the controller interface is disabled
  - phy initialisation is not complete

  RMA requests from `lcmgr` are held until other operations finish.

  Source for requirement: O RRAM Phy, F (`OP.PROTOCOL_CTRL`)

- **8.9**: Read pipeline latency and buffer states

  A read-buffer hit returns data with one cycle latency, without accessing the RRAM.
  Buffer entries move through `Invalid` → `Alloc` → `Valid` → `Verified`.
  If every entry is `Alloc` or `Valid`, new read requests stall until the shadow-read FSM promotes an entry to `Verified`.

  Source for requirement: O RRAM Read Pipeline, O RRAM Read Buffer

- **8.10**: Multi-page writes

  The `rram_phy_wr` word counter is bounded by one page (`MaxWrWords = 32` RRAM words).
  A multi-page controller write is issued to the macro as separate per-page writes.

  Source for requirement: O RRAM Write Data Path

## 9. RRAM macro interface

- **9.1**: Request signals

  The request signals in the interface are:
  - `rd_req`: read the RRAM word at `addr` in `part`.
  - `wr_req`: with `wr_last` low, push one RRAM word (`wr_data`) into the macro's store buffer.
    The word-in-page bits of `addr` select its position within the page.
  - `wr_last`: with `wr_req`, commit the store buffer to the page selected by `addr`.
    This beat carries no data.
  - `addr`: RRAM word address (128-bit granularity).
  - `wr_data` [DataWidth]: write data, already scrambled and address-infected by `rram_phy_wr`.
  - `part` (`RramPartData` or `RramPartInfo`)
  - `ecc_en`: enable ECC encoding (write) or decoding and correction (read) for this request.

  Source for requirement: T

- **9.2**: Response signals

  The response signals in the interface are:
  - `ack`: the current request was accepted.
  - `done`: the accepted request completed.
    For reads, `rd_data` and `ecc_err` are valid in the same cycle.
  - `err`: the accepted request was rejected (e.g. a commit with an empty store buffer, or a push to a full store buffer).
  - `ecc_err[2:0]`: ECC status of a read (see 9.3).
  - `rd_data`
  - `init_done`: the macro has finished initialisation (see 7a.5).
  - `fatal_err`: fatal macro-internal fault, which raises the `fatal_macro_err` alert.
  - `recov_err`: recoverable macro-internal fault, which raises the `recov_macro_err` alert.

  Source for requirement: T

- **9.3**: ECC error encoding

  `ecc_err` is one-hot0, encoded as follows:
  - 001 = single-bit corrected
  - 010 = double-bit corrected
  - 100 = uncorrectable (fatal)
  - 000 = no error

  Source for requirement: T, O

- **9.4**: Macro handshake

  A request (`rd_req` or `wr_req`) and its attributes are held stable until the macro asserts `ack`.
  Each request receives exactly one `ack`.

  Source for requirement: T

- **9.5**: Macro write sequence

  A write pushes each RRAM word of the page into the store buffer, then commits the buffer to the page with `wr_last`.

  Source for requirement: T

## 10. Interrupts

- **10.1**: There are seven interrupts that can be asserted:

  - `wr_empty` (Status)
  - `wr_lvl` (Status)
  - `rd_full` (Status)
  - `rd_lvl` (Status)
  - `op_done` (Event)
  - `corr1_err` (Event)
  - `corr2_err` (Event).

  Source for requirement: I

- **10.2**: `INTR_STATE` reset is 0x3 (`wr_empty`=1, `wr_lvl`=1).

  Source for requirement: R

- **10.3**: Level interrupts

  `wr_lvl` fires when the write FIFO level is at most `FIFO_LVL.WR`.
  `rd_lvl` fires when the read FIFO level is at least `FIFO_LVL.RD`.

  Source for requirement: R

- **10.4**: Interrupt enable / test behaviour

  `INTR_ENABLE` and `INTR_TEST` follow the standard comportable pattern.

  Source for requirement: R

## 11. Alerts, error and fault reporting

- **11.1**: Five alerts: `recov_err`, `fatal_std_err`, `fatal_err`, `fatal_macro_err`, `recov_macro_err`.

  `ALERT_TEST` bits 0–4 trigger each one.
  Bit 31 `regwen` (`rw0c`) permanently disables alert test until reset.

  Source for requirement: I, R

- **11.2**: The `recov_err` alert fires when a SW-initiated operation completes with any bit set in `ERR_CODE`.

  Source for requirement: I, O

- **11.3**: The `fatal_std_err` alert fires when any bit of `STD_FAULT_STATUS` is set.

  It covers register integrity, lcmgr, otp, phy write integrity, phy FIFO/FSM/counter/arbiter, and ctrl FSM/counter/FIFO errors.
  This is a fatal alert and cannot be cleared.

  Source for requirement: I, R

- **11.4**: The `fatal_err` alert fires when any bit of `FAULT_STATUS` is set, including uncorrectable ECC.

  This is a fatal alert and cannot be cleared.

  Source for requirement: I, R

- **11.5**: Macro error alerts

  `fatal_macro_err` covers fatal errors inside the macro, including TL-UL integrity faults on its test interface.
  `recov_macro_err` covers recoverable macro errors.

  The `fatal_macro_err` alert is fatal and cannot be cleared.

  Source for requirement: I, T

- **11.6**: `ERR_CODE` (all `rw1c`, all recoverable): `op_err`, `mp_err`, `rd_err`, `wr_err`.

  The fields of `ERR_CODE` are set when a corresponding operation completes with an error.
  `ERR_ADDR` gives the address for `rd_err`, `wr_err` and `mp_err`.
  These fields remain set until cleared by software (`rw1c` access mode).

  Source for requirement: R, P

- **11.7**: `phy_relbl_err` is clearable so firmware can deal with multi-bit ECC errors during firmware selection.

  Clearing it does not undo an escalation it already caused while `DIS.LOCAL_ESC_RELBL_ERR` was set.

  Source for requirement: I, R, O

- **11.8**: Unrecoverable error reporting

  The bits of the `FAULT_STATUS` register are:
  - `lcmgr_{op,mp,rd,wr}_err`
  - `otp_{op,mp,rd,wr}_err`
  - `seed_err`
  - `phy_relbl_err`
  - `phy_rd_intg_err`
  - `phy_rd_ctrl_err`
  - `spurious_done`
  - `host_gnt_err`.

  Source for requirement: R

- **11.9**: Errors caused by integrity mismatches

  If `ERR_CODE.rd_err` or `ERR_CODE.wr_err` was caused by an integrity mismatch, the corresponding fault bit in `STD_FAULT_STATUS`/`FAULT_STATUS` is set at the same time.
  `op_err` and `mp_err` are never caused by an integrity mismatch.

  Source for requirement: O RRAM Errors and Faults

## 12. Disable, execute and escalation controls

- **12.1**: `DIS.SW_DIS`

  This field is MuBi4, `rw1s`.
  Setting the field to any value other than MuBi4False disables RRAM completely until the next reset.
  It takes effect immediately.
  Reset value is MuBi4False (0x9).

  Source for requirement: R, O RRAM Escalation & Disable

- **12.2**: `DIS.LOCAL_ESC_RELBL_ERR`

  This field is MuBi4, `rw1s`.
  When set to anything but MuBi4False, `phy_relbl_err` disables the RRAM until reset.
  It is not revertible.
  The `fatal_err` alert is raised regardless.

  Source for requirement: R, O

- **12.3**: `EXEC.EN` (32-bit): only the magic value (`ExecEn`) allows instruction fetches from RRAM.

  Any other value (reset 0x0) prevents instruction fetches via `host_tl`.
  Data reads are not affected.

  Source for requirement: R, P Code Execution from RRAM, F (`FETCH_CODE`)

- **12.4**: Global escalation (`lc_escalate_en`) makes memory inaccessible (`MEM.CTRL.GLOBAL_ESC`).

  Source for requirement: I, T, O

- **12.5**: Local escalation: a subset of fatal errors make memory inaccessible.

  All bits of `STD_FAULT_STATUS` and `FAULT_STATUS` are in the subset, except `phy_relbl_err`.
  That bit is only included once enabled by setting `DIS.LOCAL_ESC_RELBL_ERR`.
  Local escalation takes effect one cycle after the fault is recorded.
  Once triggered, it is latched until the next reset, even if the causing fault is cleared.

  Source for requirement: I, O RRAM Escalation & Disable

- **12.6**: Effect of disable

  Once RRAM access is disabled by global escalation, local escalation or `DIS.SW_DIS`:
  - All host and controller requests are blocked (`rram_phy` suppresses new requests).
  - The scrambler switches to random keys (see 5.14).
  - The `seed_valid` bits to the key manager are cleared (see 7a.3).
  - Accesses through `otp_macro_i` / `otp_macro_o` return `MacroError`
  - The `rram_ctrl` registers remain accessible, so software can read status and error information.
  - Only a full reset restores normal operation.

  Source for requirement: O RRAM Escalation & Disable, O Stage 2

## 13. Security countermeasures (IDs from `interfaces.md`)

Grouped by type.
The prefix `RRAM_CTRL.` is omitted.

- **13.1** (Bus integrity): `REG.BUS.INTEGRITY`, `HOST.BUS.INTEGRITY`, `MEM.BUS.INTEGRITY`

  Source for requirement: I

- **13.2** (Data protection): `MEM.ADDR_INFECTION`, `MEM.SCRAMBLE`, `SCRAMBLE.KEY.SIDELOAD`, `MEM.INTEGRITY`, `OTP.MEM.INTEGRITY`, `MEM.READBACK`

  Source for requirement: I

- **13.3** (Config locking): `CTRL.CONFIG.REGWEN`, `DATA_REGIONS.CONFIG.REGWEN`, `INFO_PAGE.CONFIG.REGWEN`

  Source for requirement: I

- **13.4** (Disable and escalation): `MEM.CTRL.GLOBAL_ESC`, `MEM.CTRL.LOCAL_ESC`, `MEM_DISABLE.CONFIG.MUBI`, `EXEC.CONFIG.REDUN`, `LC_CTRL.INTERSIG.MUBI`

  Source for requirement: I

- **13.5** (Secure wipe): `RMA_ENTRY.MEM.SEC_WIPE`

  Source for requirement: I

- **13.6* (Sparse FSMs): `CTRL.FSM.SPARSE` (lcmgr, otp, arb, rd/wr), `PHY_WR.FSM.SPARSE`, `HOST_TL_LC_GATE.FSM.SPARSE`, `WR_TL_LC_GATE.FSM.SPARSE`

  Source for requirement: I

- **13.7** (Redundant counters, arbiters and FIFOs): `CTR.REDUN`, `FIFO.CTR.REDUN`, `PHY_ARBITER.CTRL.REDUN`

  Source for requirement: I

- **13.8** (Consistency checks): `PHY_HOST_GRANT.CTRL.CONSISTENCY`, `PHY_RSP.CTRL.CONSISTENCY`, `PHY_RD_RSP.CTRL.INTEGRITY`, `PHY_RD_BUF.CTRL.INTEGRITY`

  Source for requirement: I

Notes on specific countermeasures:
- `MEM.BUS.INTEGRITY`:
  - On reads, the TL-UL requester is expected to check integrity.
  - On writes, integrity is checked in `rram_phy_wr`.

- `HOST.BUS.INTEGRITY`:
  - The RRAM-to-read-buffer path is protected by the secondary (shadow) read.
  - Command integrity is checked on every `host_tl` request (see 2.8).

## 14. Register-level conventions

- **14.1**: Collisions where HW and SW write a register on the same cycle

  The registers in `rram_ctrl` behave the same as others in OpenTitan.
  The software update is applied and the hardware update is dropped.

  Source for requirement: G

- **14.2**: MuBi4 encoding is used for many enable/disable fields.

  The following register fields are represented by MuBi4 values:
  - In `DIS`, fields `LOCAL_ESC_RELBL_ERR` and `SW_DIS`
  - In `DEFAULT_REGION`, fields `ECC_EN`, `SCRAMBLE_EN`, `WR_EN` and `RD_EN`
  - In `MP_REGION_CFG_*`, fields `ECC_EN`, `SCRAMBLE_EN`, `WR_EN`, `RD_EN` and `EN`
  - In `INFO_PAGE_CFG_*`, fields `ECC_EN`, `SCRAMBLE_EN`, `WR_EN`, `RD_EN` and `EN`
  - In `EMUL_INFO_REGION_*`, the field `EN`
  - In `EMUL_INFO_SUBREGION_CFG_*`, fields `ECC_EN`, `SCRAMBLE_EN`, `WR_EN` and `RD_EN`
  - In `HW_INFO_CFG_OVERRIDE`, fields `ECC_DIS` and `SCRAMBLE_DIS`

  The reset value of 0x9 (MuBi4False) means "false"/"disabled".
  As such, the default for `EN`, `RD_EN`, `WR_EN`, `SCRAMBLE_EN`, `ECC_EN`, `DEFAULT_REGION` and `SW_DIS` is off/not-disabled as appropriate.

  Source for requirement: R

- **14.3**: All software-writable REGWEN registers are `rw0c`, reset 1, and one-way.

  Once 0 they stay locked until reset.
  Note that this doesn't apply to `CTRL_REGWEN`, which is hardware-controlled.

  Source for requirement: R

- **14.4**: `DIS` fields, `INIT.VAL` and similar are `rw1s` (set-only, one-way).

  Source for requirement: R

- **14.5**: Register access and reset values

  Registers have the reset values and addresses described in the hjson.
  They do not alias.

  Source for requirement: R

- **14.6**: Register bus integrity

  Register bus integrity is checked (`REG.BUS.INTEGRITY`).
  Errors set `STD_FAULT_STATUS.reg_intg_err`.

  Source for requirement: I, R, O

- **14.7**: Scratch register

  The `SCRATCH` register has no hardware function but can be accessed by software.

  Source for requirement: R
