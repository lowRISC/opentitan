# Programmer's Guide

## Initialization

Initialization is a two-stage process.

**Stage 1 — Wait for physical controller ready**

After reset, the RRAM macro completes its own self-initialization.
Software can monitor this via [`PHY_STATUS.init_done`](registers.md#phy_status).
Until this is set, the arbiter blocks all accesses including hardware interfaces.
In practice, firmware typically does not need to poll this directly, as stage 2 cannot complete before stage 1.

**Stage 2 — Trigger lcmgr initialization**

Software must write `1` to [`INIT.VAL`](registers.md#init) to start the lcmgr sequence.
The lcmgr will request the address and data scrambling keys from OTP, and if provisioning is enabled (`lc_seed_hw_rd_en`), read the creator and owner seed pages and forward them to the key manager.

Software should then poll [`STATUS.init_done`](registers.md#status) and wait until it reads `1` before issuing any read or write operation.
Until `STATUS.init_done` is set, all software-initiated RRAM operations are blocked by the arbiter.

## Issuing a Controller Read

To issue an RRAM read, software must:

1. Wait for any previous operation to complete (poll [`OP_STATUS.done`](registers.md#op_status) or wait for the `op_done` interrupt).
2. Write the byte address of the first bus word to read into [`ADDR`](registers.md#addr).
   The address is relative to the start of the selected partition.
   The controller truncates to the nearest lower 4-byte boundary.
3. Write [`CONTROL`](registers.md#control) with:
   - `OP = Read`
   - `NUM` = (number of bus words to read) − 1
   - `PARTITION = 0` for the data partition, `1` for the info partition
4. Set [`CONTROL.START`](registers.md#control) to begin the operation.

Once the operation starts, the controller reads RRAM and pushes 32-bit bus words into the read FIFO.
Software drains the FIFO by reading from [`rd_fifo`](registers.md#rd_fifo).

If the number of words requested exceeds the read FIFO depth (16 entries), the controller stalls automatically when the FIFO is full and resumes when space is available.
Software can use the `rd_full` or `rd_lvl` interrupts to pace FIFO draining.
When all requested words have been read, the controller sets [`OP_STATUS.done`](registers.md#op_status) and asserts the `op_done` interrupt.

See [library code](../../../../sw/device/lib/dif/dif_rram_ctrl.c) for a reference implementation.

## Issuing a Controller Write

To write RRAM, software must:

1. Wait for any previous operation to complete.
2. Write the byte address of the first RRAM word to write into [`ADDR`](registers.md#addr).
   The address must be 16-byte (128-bit) aligned; the controller truncates to the nearest lower 16-byte boundary.
3. Write [`CONTROL`](registers.md#control) with:
   - `OP = Write`
   - `NUM` = (number of bus words to write) − 1; number of bus words must be a multiple of 4 (one full RRAM word)
   - `PARTITION = 0` for the data partition, `1` for the info partition
4. Set [`CONTROL.START`](registers.md#control).
5. Push data into the write FIFO by writing to [`wr_fifo`](registers.md#wr_fifo).

If the total write count exceeds the write FIFO depth (4 entries), the controller stalls automatically when the FIFO is empty and resumes when data is available.
Software can use the `wr_empty` or `wr_lvl` interrupts to pace FIFO filling.
When all words have been programmed, the controller sets [`OP_STATUS.done`](registers.md#op_status) and asserts the `op_done` interrupt.

### Write Alignment

The minimum write granularity is one RRAM word (128 bits / 16 bytes).
Every write operation must:
- Start at a 16-byte aligned address.
- Transfer a number of bus words that is a multiple of 4 (i.e. a whole number of RRAM words).

To modify less than a full RRAM word, software must perform a read-modify-write in software: read the full word, update the desired bytes, and write the word back.

## Accessing the Information Partition

The information partition is not accessible via the host TL-UL window.
It can only be reached via the controller path (write and read FIFOs) by setting `CONTROL.PARTITION = 1`.
The address field then addresses within the info partition (0 = info page 0, word 0).

Access to each info page is controlled by the corresponding [`INFO_PAGE_CFG_*`](registers.md#info_page_cfg) register.
Pages 5 (creator seed) and 6 (owner seed) have additional life-cycle-controlled access guards; see the theory of operation.

## Configuring Memory Protection

### Data Partition

Configure up to 8 named protection regions via the [`MP_REGION_CFG_*`](registers.md#mp_region_cfg) and [`MP_REGION_*`](registers.md#mp_region) register pairs.
Each region specifies a base page, a size in pages, and access attributes (`rd_en`, `wr_en`, `scramble_en`, `ecc_en`, `addr_xor_en`).
Enable the region by setting `en = MuBi4True`.

If no active region matches an access, [`DEFAULT_REGION`](registers.md#default_region) applies.

Each region's configuration registers can be locked independently by writing 0 to the corresponding [`REGION_CFG_REGWEN_*`](registers.md#region_cfg_regwen) register.
Once locked, the region cannot be reconfigured until the next reset.

### Information Partition

Each info page is independently configured via [`INFO_PAGE_CFG_*`](registers.md#info_page_cfg), using the same access attributes as data regions.
Individual pages can be locked via [`INFO_REGWEN_*`](registers.md#info_regwen).

## Code Execution from RRAM

Instruction fetches via the host TL-UL port are disabled by default.
To enable code execution from RRAM, software must write the magic value `0xa26a38f7` to the [`EXEC`](registers.md#exec) register.
Any other value disables instruction fetches.

This register is guarded by a redundancy check ([`EXEC.CONFIG.REDUN`](../README.md#security-countermeasures)); only the correct magic value enables execution.

## Debugging Read Errors

### Error Encountered by Host Direct Read

If software reads RRAM directly via the host TL-UL port, it may encounter ECC failures or read data integrity errors.
Correctable ECC errors are fixed transparently; the `corr_err` interrupt is asserted and the address of the corrected error is recorded in [`CORR_ERR_LOC`](registers.md#corr_err_loc).
Uncorrectable ECC errors or integrity failures produce in-band TL-UL error responses and may trigger a processor exception.
Software can determine the failing address through processor-specific means.

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

### Hardware Initiated Reads

If the root secrets have been provisioned and the life cycle state enables provisioning (`lc_seed_hw_rd_en`), the creator and owner seed pages in the info partition are read automatically during initialization and forwarded to the key manager.
These pages must be initialized with valid, scrambled data before the device enters a provisioned life cycle state.

By default, hardware assumes scrambling and ECC are enabled on these pages.
If software provisions these pages without scrambling or ECC, the [`HW_INFO_CFG_OVERRIDE`](registers.md#hw_info_cfg_override) register must be updated accordingly before the next reset to prevent a configuration mismatch during hardware readout.

### Correctable ECC Errors

Correctable ECC errors are not fatal; the controller fixes the data in place and continues.
The `corr_err` interrupt fires and the error counter is incremented in [`CORR_ERR_CNT`](registers.md#corr_err_cnt).
The address and partition of the last corrected error are recorded in [`CORR_ERR_LOC`](registers.md#corr_err_loc).

Persistent correctable errors at the same address may indicate RRAM cell degradation and should be monitored.
A rewrite operation (`CONTROL.OP = Rewrite`) can be used to restore a degraded word by reading and writing it back.

### Errors During Multi-Word Controller Reads

Upon encountering the first error during a multi-word read, the RRAM controller transitions to an error state (`StErr`) and stops issuing new RRAM read requests.
It still returns the full requested number of words to avoid leaving the read FIFO in a state that would deadlock software.
For the word where the error occurred, the actual RRAM data is returned.
For all subsequent words, the controller returns all-ones (`0xFFFFFFFF`) with valid bus integrity — no further RRAM accesses are made and no data from other concurrent operations can appear.

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
