# Programmer's Guide

## Initialization

Initialization is a two-stage process.
See [Initialization](theory_of_operation.md#initialization) in the theory of operation for the full stage 1/2 sequence.

### Auto-initialization - Wait for RRAM phy ready

After reset, the RRAM macro completes its own self-initialization.
Software can monitor this via [`PHY_STATUS.init_done`](registers.md#phy_status).
Until this is set, the arbiter blocks all accesses including hardware interfaces.
In practice, firmware typically does not need to poll this directly, as stage 2 cannot complete before stage 1.

### Controller initialization - Trigger controller initialization

Software must write `1` to [`INIT.VAL`](registers.md#init) to start the controller's initialization sequence.
During this initialization, the address and data scrambling keys are requested from OTP and, if provisioning is enabled (`lc_seed_hw_rd_en`), the creator and owner seed pages are read and forwarded to the key manager.

Software should then poll [`STATUS.init_done`](registers.md#status) and wait until it reads `1` before issuing any read or write operation.
Until `STATUS.init_done` is set, all software-initiated RRAM operations are blocked by the arbiter.

## Memory-Mapped Reads via `host_tl`

The CPU can read RRAM directly through the `host_tl` TL-UL interface, memory-mapped into the system address space.

Only the data partition is accessible this way.
The OTP region (the reserved top pages of the data partition) is not reachable.
See [Memory Protection for OTP Hardware Plug](theory_of_operation.md#memory-protection-for-otp-hardware-plug) in the theory of operation for the enforcement mechanism.
The information partition is likewise not accessible via `host_tl`.

See the [Address Map](../README.md#address-map) table in the README for the full data/OTP/info partition byte-address layout and per-region accessibility.

`host_tl` reads are subject to the same memory protection as the controller-path.
See [Configuring Memory Protection](#configuring-memory-protection) for details.

### Code Execution from RRAM

Instruction fetches via the host TL-UL port are disabled by default.
To enable code execution from RRAM, software must write the magic value `0xa26a38f7` to the [`EXEC`](registers.md#exec) register.
Any other value disables instruction fetches.
The exact value has no special meaning beyond acting as a multibit enable pattern.

This register is guarded by a redundancy check ([`EXEC.CONFIG.REDUN`](interfaces.md#security-countermeasures)).
Only the correct magic value enables execution.

## Issuing a Controller Read

The target region or info page must be configured to permit the access.
See [Configuring Memory Protection](#configuring-memory-protection) for details.
Otherwise, the operation completes with `mp_err` set.
See [Error Encountered by Software Initiated Controller Operations](#error-encountered-by-software-initiated-controller-operations) for details.

To issue an RRAM read, software must:

1. Wait for any previous operation to complete (poll [`OP_STATUS.done`](registers.md#op_status) or wait for the `op_done` interrupt).
2. Write the byte address of the first bus word to read into [`ADDR`](registers.md#addr).
   The address is relative to the start of the selected partition.
   The controller truncates to the nearest lower 4-byte boundary.
3. Write [`CONTROL`](registers.md#control) with:
   - `OP = Read`
   - `NUM` = (number of bus words to read) - 1
   - `PARTITION = 0` for the data partition, `1` for the info partition
4. Set [`CONTROL.START`](registers.md#control) to begin the operation.

Once the operation starts, the controller reads from the RRAM and pushes 32-bit bus words into the read FIFO.
The software drains the FIFO by reading from [`rd_fifo`](registers.md#rd_fifo).

If the number of words requested exceeds the read FIFO depth, the controller stalls automatically when the FIFO is full and resumes when space is available.
Software can use the `rd_full` or `rd_lvl` interrupts to pace FIFO draining.
When all requested words have been read, the controller sets [`OP_STATUS.done`](registers.md#op_status) and asserts the `op_done` interrupt.

See [library code](../../../../sw/device/lib/dif/dif_rram_ctrl.c) for a reference implementation.

## Issuing a Controller Write

The target region or info page must be configured to permit the access.
See [Configuring Memory Protection](#configuring-memory-protection) for details.
Otherwise, the operation completes with `mp_err` set.
See [Error Encountered by Software Initiated Controller Operations](#error-encountered-by-software-initiated-controller-operations) for details.

To write RRAM, software must:

1. Wait for any previous operation to complete.
2. Write the byte address of the first RRAM word to write into [`ADDR`](registers.md#addr).
   The address must be 16-byte (128-bit) aligned.
   The controller truncates to the nearest lower 16-byte boundary.
3. Write [`CONTROL`](registers.md#control) with:
   - `OP = Write`
   - `NUM` = (number of bus words to write) - 1.
     The number of bus words must be a multiple of 4 (one full RRAM word).
   - `PARTITION = 0` for the data partition, `1` for the info partition
4. Set [`CONTROL.START`](registers.md#control).
   This clears the write FIFO, discarding any data pushed to it earlier.
5. Push data into the write FIFO by writing to [`wr_fifo`](registers.md#wr_fifo).
   Data must be pushed after the start has been sent.

If the total write count exceeds the write FIFO depth, the controller stalls automatically when the FIFO is empty and resumes when data is available.
Software can use the `wr_empty` or `wr_lvl` interrupts to pace FIFO filling.
When all words have been programmed, the controller sets [`OP_STATUS.done`](registers.md#op_status) and asserts the `op_done` interrupt.

### Write Alignment

The minimum write size is one RRAM word (128 bits / 16 bytes).
Every write operation must:
- Start at a 16-byte aligned address.
- Transfer a number of bus words that is a multiple of 4 (i.e. a whole number of RRAM words).

To modify less than a full RRAM word, software must perform a read-modify-write: read the full word, update the desired bytes, and write the word back.

## Issuing a Rewrite Operation

A degraded RRAM word can be restored with a rewrite operation, typically after a `corr_err` interrupt.
See [Correctable ECC Errors](#correctable-ecc-errors) for details.
To issue a rewrite, software must:

1. Wait for any previous operation to complete.
2. Write the byte address of the word to rewrite into [`ADDR`](registers.md#addr), typically taken from [`CORR_ERR_LOC`](registers.md#corr_err_loc).
3. Write [`CONTROL`](registers.md#control) with:
   - `OP = Rewrite`
   - `PARTITION = 0` for the data partition, `1` for the info partition
   - `NUM` is ignored.
     The hardware always reads and writes back exactly one full RRAM word (4 bus words / 16 bytes), regardless of its value.
4. Set [`CONTROL.START`](registers.md#control) to begin the operation.

Internally, the controller reads the addressed RRAM word and immediately writes the same data back, without exposing it to software or the read/write FIFOs.
When complete, the controller sets [`OP_STATUS.done`](registers.md#op_status) and asserts the `op_done` interrupt, the same as for a Read or Write operation.
If the internal read or write fails, [`OP_STATUS.err`](registers.md#op_status) is set and the failure is reported through [`ERR_CODE`](registers.md#err_code)/[`ERR_ADDR`](registers.md#err_addr), exactly as for a normal read or write error.

## Accessing the OTP Region

The OTP region is not directly programmable through `rram_ctrl`'s `CONTROL`/`ADDR` registers or FIFOs.
There is no software-facing `OP` value for OTP read/write.
Instead, `otp_ctrl` itself issues `OtpRead`/`OtpWrite`/`OtpReadRaw`/`OtpWriteRaw`/`OtpInit`/`OtpZeroize` commands to the `rram_ctrl_otp` hardware plug, which uses the OTP region as its NVM backing store.
Software that wishes to read or write OTP data must use `otp_ctrl`'s own interface.
See its [Direct Access Interface](../../../top_earlgrey/ip_autogen/otp_ctrl/doc/programmers_guide.md#direct-access-interface) programmer's guide.

### Errors on the OTP Interface

A memory protection, read, write, or undefined-operation error on the `rram_ctrl_otp` hardware interface is reported in [`FAULT_STATUS`](registers.md#fault_status):

| Field | Meaning |
|---|---|
| `otp_op_err` | Undefined operation issued |
| `otp_mp_err` | Memory protection violation |
| `otp_rd_err` | RRAM read error (ECC or integrity failure) |
| `otp_wr_err` | RRAM write error |

A fatal FSM, count or a transmission-integrity error on the same interface is reported in [`STD_FAULT_STATUS.otp_err`](registers.md#std_fault_status) / [`STD_FAULT_STATUS.otp_intg_err`](registers.md#std_fault_status).

## Configuring Memory Protection

### Data Partition

Configure up to 10 named protection regions via the [`MP_REGION_CFG_*`](registers.md#mp_region_cfg) and [`MP_REGION_*`](registers.md#mp_region) register pairs.
Each region specifies a base page, a size, and access attributes (`rd_en`, `wr_en`, `scramble_en`, `ecc_en`).
The size is one less than the number of pages in the region, i.e. `SIZE = pages - 1`, since the region covers `[BASE, BASE + SIZE]` inclusive.
Enable a region by setting `en = MuBi4True`.
On reset, all regions are disabled (`en = MuBi4False`).
Software must explicitly enable and configure each region before use.

If no active region matches an access, the properties from [`DEFAULT_REGION`](registers.md#default_region) apply.
On reset, `DEFAULT_REGION` denies all access (`rd_en`, `wr_en`, `scramble_en`, and `ecc_en` are all `MuBi4False`).
Software must reconfigure it to match the intended security policy before relying on the fallback path.

Each region's configuration registers can be locked independently by writing 0 to the corresponding [`REGION_CFG_REGWEN_*`](registers.md#region_cfg_regwen) register.
Once locked, the region cannot be reconfigured until the next reset.

### Information Partition

The information partition is not accessible via the host TL-UL window.
It can only be reached via the controller path by setting `CONTROL.PARTITION = 1`.
It addresses independently from the data partition: page 0, word 0 of the info partition is address `0x000000`.

Each info page is independently configured via [`INFO_PAGE_CFG_*`](registers.md#info_page_cfg), using the same access attributes as data regions.
On reset, each info page is disabled (`en = MuBi4False`).
A page can only be accessed after software has explicitly programmed the page's `INFO_PAGE_CFG_*` register.
Individual pages' configuration can be locked via [`INFO_REGWEN_*`](registers.md#info_regwen).

Pages 5 (creator seed), 6 (owner seed), and 7 (isolated partition) additionally have a life-cycle-controlled signal ANDed with their `rd_en`/`wr_en`.
Both `INFO_PAGE_CFG_*` and the life cycle signal must permit the access, so life cycle can only further restrict access, never grant it beyond what `INFO_PAGE_CFG_*` allows.
See [Memory Protection for LCMGR Hardware Plug](theory_of_operation.md#memory-protection-for-lcmgr-hardware-plug) in the theory of operation for details.

## Debugging Errors

### Error Encountered by Host Direct Read

If software reads RRAM directly via the host TL-UL port, it may encounter ECC failures or read data integrity errors.
Correctable ECC errors are fixed transparently.
The `corr_err` interrupt is asserted and the address of the corrected error is recorded in [`CORR_ERR_LOC`](registers.md#corr_err_loc).
Uncorrectable ECC errors or integrity failures produce in-band TL-UL error responses which will trigger a processor exception.

### Error Encountered by Software Initiated Controller Operations

When a controller operation completes with [`OP_STATUS.err`](registers.md#op_status) set, software should inspect [`ERR_CODE`](registers.md#err_code) to identify the error category:

| Field | Meaning |
|---|---|
| `op_err` | Undefined operation supplied in `CONTROL.OP` (see register description for valid values) |
| `mp_err` | Memory protection violation |
| `rd_err` | RRAM read error (ECC or integrity failure) |
| `wr_err` | RRAM write error |

[`ERR_ADDR`](registers.md#err_addr) records the address at which the first error was encountered.
For multi-word operations, the controller aborts at the first error but the FIFO may still contain partially valid data.

#### Errors During Multi-Word Controller Reads

Upon encountering the first error during a multi-word read, the RRAM controller transitions to an error state (`StErr`) and stops issuing new RRAM read requests.
It still returns the full requested number of words to avoid leaving the read FIFO in a state that would deadlock software.
Starting with the word where the error occurred, the controller returns all-ones (`0xFFFFFFFF`) with valid bus integrity for that word and every subsequent word.
No further RRAM accesses are made, and no data from other concurrent operations can appear.

### Errors Encountered During Hardware Initiated Operations

The creator and owner seed pages (see [Controller initialization](#controller-initialization---trigger-controller-initialization) for when they are read) must be initialized with valid, scrambled data before the device enters a provisioned life cycle state.

An error in the hardware-initiated seed read itself is reported in [`FAULT_STATUS.seed_err`](registers.md#fault_status).
A memory protection, read, write, or undefined-operation error on the life cycle management interface is reported in [`FAULT_STATUS`](registers.md#fault_status):

| Field | Meaning |
|---|---|
| `lcmgr_op_err` | Undefined operation issued |
| `lcmgr_mp_err` | Memory protection violation |
| `lcmgr_rd_err` | RRAM read error (ECC or integrity failure) |
| `lcmgr_wr_err` | RRAM write error |

A fatal FSM, count or a transmission-integrity error on the same interface is reported in [`STD_FAULT_STATUS.lcmgr_err`](registers.md#std_fault_status) / [`STD_FAULT_STATUS.lcmgr_intg_err`](registers.md#std_fault_status).

By default, hardware assumes scrambling and ECC are enabled on these pages.
If software provisions these pages without both scrambling and ECC enabled, the [`HW_INFO_CFG_OVERRIDE`](registers.md#hw_info_cfg_override) register must be updated accordingly when initializing the controller, to prevent a configuration mismatch during hardware readout.

### Correctable ECC Errors

Correctable ECC errors are not fatal.
The controller fixes the data in place and continues.
The `corr_err` interrupt fires and the error counter is incremented in [`CORR_ERR_CNT`](registers.md#corr_err_cnt).
The address and partition of the last corrected error are recorded in [`CORR_ERR_LOC`](registers.md#corr_err_loc).
See [Single-Bit Error (Correctable)](theory_of_operation.md#single-bit-error-correctable) in the theory of operation for a known limitation of this mechanism.

On `corr_err`, software can attempt to fix the affected word by issuing a [Rewrite operation](#issuing-a-rewrite-operation) at the address recorded in `CORR_ERR_LOC`.
If correctable errors keep recurring at the same address, this may indicate RRAM cell degradation.

## Scrambling Consistency

The RRAM macro does not store whether a given location was written with scrambling enabled or disabled.
Software must ensure the `scramble_en` attribute in the protection region or info-page configuration is **consistent between all reads and writes to a given page**.
Writing with `scramble_en = true` and reading with `scramble_en = false` (or vice versa) will produce garbage data with no error indication.

## FIFO Management

The current FIFO depths are available in [`CURR_FIFO_LVL`](registers.md#curr_fifo_lvl).
The interrupt watermarks for `wr_lvl` and `rd_lvl` are configured in [`FIFO_LVL`](registers.md#fifo_lvl).
Both FIFOs can be flushed via [`FIFO_CLR`](registers.md#fifo_clr).

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_rram_ctrl.h)
