# RRAM Controller HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/rram_ctrl/data/rram_ctrl.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`rram_ctrl`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 1.0.0 | D1, V0 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rram_ctrl/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rram_ctrl/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rram_ctrl/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/rram_ctrl/code.svg) |

<!-- END CMDGEN -->

# Overview

This document describes the RRAM Controller hardware IP functionality.
The RRAM Controller is a comportable IP that manages access to an integrated resistive RAM (RRAM) macro.
It must be used in conjunction with the RRAM macro and cannot be used standalone.

The controller is structurally similar to the Flash Controller and offers comparable functionality: host-side read-only memory-mapped access, software-initiated read and write transactions via FIFOs, memory protection, hardware-accelerated scrambling, and secure hardware interfaces to the OTP controller, key manager and life cycle controller.

This module conforms to the [Comportable guideline for peripheral functionality](https://opentitan.org/book/doc/contributing/hw/comportability).
See that document for integration overview within the broader top-level system.

## RRAM Subsystem

The RRAM subsystem provides the non-volatile storage capabilities for OpenTitan.
It consists of a single RRAM macro together with a dedicated controller:

<img src="doc/rram_subsystem.svg" width="800"/>

### rram_ctrl (Open Source)

A controller maintaining functionality and security features closely aligned with the original `flash_ctrl`, with the additional capability of performing read-set-write operations on the RRAM to support emulated OTP functionality.
It operates on 32-bit bus words, and instantiates the RRAM phy (`rram_phy`) as a sub-entity to interface with the 128-bit-wide RRAM macro.

- **RRAM controller**: Arbitrates between three sources: a software-controlled interface and two hardware interfaces (life cycle manager and OTP hardware interface).
  All three sources share the `wr_fifo`, `ctrl_rd`, and `ctrl_wr` modules and pass through the memory protection module (`rram_ctrl_mp`).
  The hardware interfaces use fixed compile-time protection rules.
  The software interface uses a mix of software-configured and hardware-overridden rules.
- **RRAM phy**: Operates on 128-bit RRAM words.
  Arbitrates between the read-only host TL-UL interface and the muxed controller interface.
  All read requests go through `rram_phy_rd`, which fetches data from the RRAM macro and caches it in the read buffers.
  Write requests go through `rram_phy_wr`, which packs bus words into RRAM words, scrambles them, and issues write requests to the RRAM macro.
  Both data paths share a single scrambling module (`rram_scramble`) capable of both scrambling and descrambling.

### rram_macro

This module exists in two forms:

- **Vendor implementation**: Closed-source, high-density RRAM with a vendor controller, reliability ECC encoding/decoding, and built-in self-test.
  Contains a register bank for device-specific configuration such as macro clock speed.
  This form is used in the physical ASIC.
- **Emulation model**: Open-source, behavioural model for simulation and FPGA prototyping.
  The RRAM data and info arrays are emulated with SRAMs.
  Each word is protected by a per-page-configurable ECC, using two independent Hamming(72,64) SECDED codes (one per 64-bit half).
  Test circuits are not connected.

The full subsystem interacts with the power manager (`pwrmgr`), key manager (`keymgr_dpe`), OTP controller (`otp_ctrl`), and life cycle controller (`lc_ctrl`).


## Features

The RRAM Controller supports read and write commands to the RRAM macro.
It has two TL-UL interfaces. `core_tl` is used to access the register bank and the FIFOs, which can reach both the data and information partitions.
`host_tl` is a read-only interface limited to the data partition.
The RRAM Controller interacts with several other hardware IPs such as the life cycle controller, OTP controller, and key manager.

### RRAM Controller Features

The RRAM controller sits between the software interface, other hardware IPs, and the RRAM phy.

- Two TL-UL interfaces:
  - `core_tl`: register access, FIFO access, and software-initiated transactions.
  - `host_tl`: read-only memory-mapped access to the data partition, for instruction fetch and direct data reads.
  - Both check the command integrity of every request.
    A failing check returns an error response and is a fatal fault, see [Transmission Integrity Faults](doc/theory_of_operation.md#transmission-integrity-faults).
- Software-initiated read, write and rewrite operations via a FIFO-based protocol.
  - Write and read FIFOs with configurable depth and interrupt watermarks.
  - Data written to the write FIFO while no software operation is in progress is discarded, see [Issuing a Controller Write](doc/programmers_guide.md#issuing-a-controller-write).
  - Burst writes must be a multiple of 4 bus words (16 bytes) and address-aligned to 16 bytes.
  - Maximum of 1024 bus words per transaction.
- Separate data and information partitions.
  - 10 configurable memory protection (MP) regions for the data partition.
  - A default region configuration applies when no region rule matches.
  - Per-page protection for the information partition.
  - Two emulated info page windows on the data partition, each with up to 12 independently
    lockable subregions, for info-page-like storage beyond the RRAM's 8 physical info pages.
    Host access to these windows is always blocked.
- XEX scrambling using the PRINCE cipher (similar construction to original flash_ctrl).
  - Scrambling is optional and independently configurable per region or info page.
  - Scrambling keys are sideloaded from emulated OTP through `otp_ctrl` and `rram_ctrl_otp`.
    Software cannot read them.
- Address-XOR integrity: each bus word is XORed with its bus-word address before storage, preventing silent relocation attacks.
  - Disabled for OTP-partition accesses, where data is already integrity-protected.
- ECC: leverages the RRAM macro's own error detection and correction logic, configurable per MP region or info page.
  - Correctable ECC errors assert `corr1_err` (single-bit) or `corr2_err` (double-bit) and increment a matching error counter.
- Emulated OTP functionality via a dedicated hardware plug (`rram_ctrl_otp`).
  - Implements OTP semantics (bits can only be set, never cleared) using a read-set-write algorithm on the reserved OTP partition.
  - Supports `OtpRead`, `OtpWrite`, `OtpReadRaw`, `OtpWriteRaw`, `OtpInit`, and `OtpZeroize` commands.
- Integrity protection for OTP read and write operations.
  - An 8-bit Hamming integrity value is stored per 64 bits of OTP data in a separate integrity page.
  - `OtpRead` recomputes and checks the integrity.
    `OtpWrite` updates both the data word and the integrity word atomically.
- Semi-automatic rewrite operation for correcting single- and double-bit ECC errors.
  - Software can issue a `Rewrite` operation (`CONTROL.OP = Rewrite`) at any time.
  - The controller reads one RRAM word and writes the corrected data back to restore full ECC headroom before further bit flips make the word uncorrectable.
  - Software typically issues it after `corr1_err` or `corr2_err` fires, at the address captured in `CORR1_ERR_LOC` or `CORR2_ERR_LOC`.
- Secure wipe upon RMA request from the life cycle controller.
  - The `rram_ctrl_lcmgr` FSM overwrites three info pages and all data partition pages except the OTP region with pseudo-random data from a 64-bit LFSR.
    The three info pages are the creator seed page, the owner seed page and the isolated page.
    It then asserts `rma_ack`.
    See [RMA Handling](doc/theory_of_operation.md#rma-handling).
  - RRAM access is permanently disabled after RMA completes until the next reset.
- Seven interrupts: `wr_empty`, `wr_lvl`, `rd_full`, `rd_lvl`, `op_done`, `corr1_err`, `corr2_err`.
- Five alerts: `recov_err`, `fatal_std_err`, `fatal_err`, `fatal_macro_err`, `recov_macro_err`.
- Software control of code execution from RRAM (`EXEC` register, guarded by a magic value).
- Idle indication to the power manager (`pwrmgr`), to prevent power-down during a write or OTP operation.

### RRAM phy (`rram_phy`) features

`rram_phy` bridges the bus-width (32-bit) RRAM controller and the wider (128-bit) RRAM macro word.

- Read buffer: 4 entries, each caching one full RRAM word (128 bits / 4 bus words).
  Acts as a miniature read-only cache to avoid re-fetching the same RRAM word for sub-word accesses.
  Buffer entries are invalidated on any write to the same RRAM page.
- Every RRAM read is issued twice (shadow read).
  If the two results differ, a fatal alert is raised.
- Up to 2 outstanding host read requests tracked through the read pipeline.
- XEX scrambling engine, shared between reads and writes and based on PRINCE.
- Address-XOR applied per bus word at the physical layer during write, and inverted during read.

### RRAM Controller - Macro Interface

`rram_ctrl` is connected to `rram_macro` via the `rram_macro_o`/`rram_macro_i` ports, using the following generic interface, which maps to both the vendor ASIC implementation and the open-source emulation model:

```systemverilog
typedef struct packed {
  logic                 rd_req;
  logic                 wr_req;
  logic                 wr_last;
  logic [AddrW-1:0]     addr;
  logic [DataWidth-1:0] wr_data;
  rram_part_e           part;    // RramPartData or RramPartInfo
  logic                 ecc_en;
} rram_macro_req_t;

typedef struct packed {
  logic                 ack;
  logic                 done;
  logic                 err;
  logic [2:0]           ecc_err; // 001: single-bit corrected,  010: double-bit corrected,
                                 // 100: uncorrectable (fatal), 000: no error
  logic [DataWidth-1:0] rd_data;
  logic                 init_done;
  logic                 fatal_err;
  logic                 recov_err;
} rram_macro_rsp_t;
```

The request fields have the following meaning:

| Field | Description |
|-|-|
| `rd_req` | Read the RRAM word at `addr` in `part`. |
| `wr_req` | With `wr_last` low, push one RRAM word (`wr_data`) into the macro's store buffer. The word-in-page bits of `addr` select its position within the page. |
| `wr_last` | With `wr_req`, commit the store buffer to the page selected by `addr`. This beat carries no data. |
| `addr` | RRAM word address (128-bit granularity). |
| `wr_data` | Write data. It is already scrambled and address-infected by `rram_phy_wr`. |
| `part` | Partition, `RramPartData` or `RramPartInfo`. |
| `ecc_en` | Enable ECC encoding (write) or ECC decoding and correction (read) for this request. |

The response fields have the following meaning:

| Field | Description |
|-|-|
| `ack` | The current request was accepted. Each request receives exactly one `ack`. |
| `done` | The accepted request completed. For reads, `rd_data` and `ecc_err` are valid in the same cycle. |
| `err` | The accepted request was rejected, e.g. a commit with an empty store buffer or a push to a full store buffer. |
| `ecc_err` | One-hot0 ECC status of a read. `000`: no error. `001`: one bit corrected. `010`: two bits corrected. `100`: uncorrectable error. |
| `rd_data` | Read data. |
| `init_done` | The macro has finished its initialization. `rram_phy` does not issue requests before. |
| `fatal_err` | Fatal macro-internal fault. Raises the `fatal_macro_err` alert. |
| `recov_err` | Recoverable macro-internal fault. Raises the `recov_macro_err` alert. |

A request (`rd_req` or `wr_req`) and its attributes are held stable until the macro asserts `ack`.
The macro only accepts a new request once the previous one has completed with `done`.
In the waveforms below, a read takes a few cycles and a store-buffer push one cycle, while the gap in the write waveform marks the much longer write latency.
All latencies depend on the macro implementation.
`A0` and `A1` are RRAM word addresses, `D0` and `D1` the corresponding data words, and `page` is the address of the page the store buffer is committed to.

A read returns the data and its ECC status together with `done`.
In this example, the macro asserts `ack` only in the second cycle of the request, so `rd_req` is held for two cycles:

```wavejson
{
  signal: [
    {name: 'clk_i',               wave: 'p.......'},
    {name: 'rd_req',              wave: '01.0....'},
    {name: 'addr / part / ecc_en', wave: 'x3.x....', data: ['A0']},
    {name: 'ack',                 wave: '0.10....'},
    {name: 'done',                wave: '0....10.'},
    {name: 'rd_data',             wave: 'x....3x.', data: ['D0']},
    {name: 'ecc_err',             wave: 'x....3x.', data: ['000']},
  ],
  head: {text: 'Read'}
}
```

A write first pushes each RRAM word into the store buffer and then commits the buffer to the page with `wr_last`:

```wavejson
{
  signal: [
    {name: 'clk_i',   wave: 'p........|..'},
    {name: 'wr_req',  wave: '010.10.10|..'},
    {name: 'wr_last', wave: '0......10|..'},
    {name: 'addr',    wave: 'x3x.3x.3x|..', data: ['A0', 'A1', 'page']},
    {name: 'wr_data', wave: 'x3x.3x...|..', data: ['D0', 'D1']},
    {name: 'ack',     wave: '010.10.10|..'},
    {name: 'done',    wave: '0.10.10..|10'},
  ],
  head: {text: 'Write of two RRAM words'}
}
```

### System Interactions

In addition to the TileLink interfaces, `rram_ctrl` directly interacts with several other OpenTitan modules.
The [block diagram](doc/theory_of_operation.md#block-diagram) labels the various life cycle signals collectively as `lc_cfg`, and the OTP interface as `otp_req`/`otp_rsp`.
See below for the individual signal and interface names.

**`lc_ctrl`**

`lc_ctrl` decodes the life cycle state and forwards the following control signals to `rram_ctrl`.
The corresponding accesses are only possible while the enable is `On`:
- `lc_creator_seed_sw_rw_en`: software read and write of the creator seed page.
- `lc_owner_seed_sw_rw_en`: software read and write of the owner seed page.
- `lc_iso_part_sw_rd_en`: software read of the isolated page.
- `lc_iso_part_sw_wr_en`: software write of the isolated page.
- `lc_seed_hw_rd_en`: the creator and owner seeds are read during initialization and forwarded to `keymgr_dpe`.

The software enables are ANDed with the software-configured page permissions, so software can only restrict access further.
See [Memory Protection for LCMGR Hardware Plug](doc/theory_of_operation.md#memory-protection-for-lcmgr-hardware-plug).

In addition, `lc_ctrl` drives `lc_escalate_en`, which disables all RRAM accesses, and issues RMA requests (`rma_req`/`rma_ack`) that trigger a secure wipe of the RRAM.

**`otp_ctrl`**
- Issues `OtpInit`, `OtpRead`, `OtpWrite`, and `OtpZeroize` commands to `rram_ctrl_otp` instead of a dedicated OTP macro, using the OTP region of the RRAM as NVM backing storage.
- Provides the scrambling keys for `rram_ctrl` derived from seeds stored in the OTP region.
- Commands are issued via the `otp_ctrl_macro_req_t`/`otp_ctrl_macro_rsp_t` interface (`otp_macro_i`/`otp_macro_o`), defined in [`otp_ctrl_macro_pkg`](../../top_earlgrey/ip_autogen/otp_ctrl/rtl/otp_ctrl_macro_pkg.sv), the same interface a standalone `otp_macro` would implement:

```systemverilog
typedef struct packed {
  logic            valid;
  cmd_e            cmd;
  otp_macro_size_t size;
  otp_macro_addr_t addr;
  otp_macro_data_t wdata;
} otp_ctrl_macro_req_t;

typedef struct packed {
  logic            ready;
  logic            rvalid;
  otp_macro_data_t rdata;
  err_e            err;
  logic            fatal_lc_fsm_err;
  logic            fatal_alert;
  logic            recov_alert;
} otp_ctrl_macro_rsp_t;
```

- Both interfaces towards `otp_ctrl` are synchronous to `clk_otp_i`/`rst_otp_ni`.
  These are `otp_macro_i`/`otp_macro_o`, handled by `rram_ctrl_otp`, and the scrambling key request `otp_key_o`/`otp_key_i`, handled by `rram_ctrl_lcmgr`.
  Everything else in `rram_ctrl` is synchronous to `clk_i`.
  `rram_ctrl_otp` crosses the clock domains with an asynchronous FIFO in each direction, and `rram_ctrl_lcmgr` with a req/ack synchronizer.

**`pwrmgr`**
- `rram_ctrl` asserts an idle signal to the power manager when it is safe to power down, i.e. when no write operation is in progress.

**`keymgr_dpe`**
- During initialisation, `rram_ctrl` reads the owner and creator seeds from predefined info pages and forwards them to the key manager.

`rram_ctrl` also connects to the alert handler and generates interrupts in the standard comportable manner.
See [Interrupts](#interrupts) and [Alerts](#alerts) for details.

### RRAM Memory Overview

The RRAM macro has two partitions: a **data partition** and an **info partition**.
The data partition contains a protected OTP region at the top of its address space, accessible only via the `rram_ctrl_otp` hardware interface.

<img src="doc/rram_organization.svg" width="800"/>

The figure shows the two physical arrays of the macro on the left: a 2 MiB data array and a 4 KiB info array.
The right side shows how `rram_ctrl` uses them.

The data partition holds general-purpose non-volatile storage.
Its top 6 pages (3 KiB) form the OTP region, which acts as NVM backing storage for the OTP controller.
The OTP region is inaccessible to software.
Software-initiated controller operations to it fail with a memory protection error, host reads to it return a TL-UL error, and the RMA wipe does not touch it.
See [Memory Protection for OTP Hardware Plug](doc/theory_of_operation.md#memory-protection-for-otp-hardware-plug).
The info partition holds design-specific data, including the two secret seed pages (creator/owner) and an isolated page for manufacturing authentication.

#### Address Map

The RRAM address space is byte-addressed.
Each RRAM word is 16 bytes (128 bits).
Each page contains 32 words (512 bytes).


The data and info partitions are separate, independently-addressed spaces.
Software selects between them via `CONTROL.PARTITION`, and each address range below starts again at `0x000000` within its own partition.

| Partition | Page | Word | Start address | Accessible by |
|-----------|------|------|-------------|---------------|
| Data | 0 | 0 | `0x000000` | Host, SW, lcmgr-hw-if |
| Data | 0 | 1 | `0x000010` | Host, SW, lcmgr-hw-if |
| Data | ... | ... | ... | ... |
| Data | 0 | 31 | `0x0001F0` | Host, SW, lcmgr-hw-if |
| Data | 1 | 0 | `0x000200` | Host, SW, lcmgr-hw-if |
| Data | ... | ... | ... | ... |
| Data | 4089 | 31 | `0x1FF3F0` | Host, SW, lcmgr-hw-if |
| Data (OTP integrity) | 4090 | 0 | `0x1FF400`<br>(`OtpIntgStartAddr`) | otp-hw-if |
| Data (OTP integrity) | ... | ... | ... | ... |
| Data (OTP integrity) | 4090 | 31 | `0x1FF5F0` | otp-hw-if |
| Data (OTP) | 4091 | 0 | `0x1FF600`<br>(`OtpStartAddr`) | otp-hw-if |
| Data (OTP) | ... | ... | ... | ... |
| Data (OTP) | 4095 (last page) | 31 (last word) | `0x1FFFF0` | otp-hw-if |
| Info | 0 | 0 | `0x000000` | SW, lcmgr-hw-if |
| Info | ... | ... | ... | ... |
| Info | 5 (`CreatorInfoPage`) | 0 | `0x000A00` | SW, lcmgr-hw-if |
| Info | 6 (`OwnerInfoPage`) | 0 | `0x000C00` | SW, lcmgr-hw-if |
| Info | 7 (`IsolatedInfoPage`, last page) | 0 | `0x000E00` | SW, lcmgr-hw-if |

When accessed by the host TL-UL interface, RRAM's base address in the system memory map (defined by the top-level address map) should be added to the byte addresses in the table above.

### Security Countermeasures

See [Security Countermeasures](doc/interfaces.md#security-countermeasures) in the interfaces documentation for the full list.

## Registers

See [registers](doc/registers.md) for the full register description.

## Interrupts

See [Interrupts](doc/interfaces.md#interrupts) in the interfaces documentation for the full list.

## Alerts

See [Security Alerts](doc/interfaces.md#security-alerts) in the interfaces documentation for the full list.
