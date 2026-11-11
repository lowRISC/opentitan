# RRAM macro HWIP Technical Specification

# Overview

This document specifies the RRAM macro hardware IP functionality.
The RRAM macro is a comportable IP that emulates a real RRAM macro.
This block is expected to be used in conjunction with the RRAM controller and cannot be used standalone.

## Features

The RRAM macro supports read and write commands to the RRAM.
Each RRAM word is protected by ECC, configurable per request via `ecc_en`.
In the open-source version, the RRAM is emulated with prim_ram_1p modules, and the ECC is two independent Hamming(72,64) SECDED codes (one per 64-bit half of the 128-bit word).
In the closed-source version, the real RRAM is instantiated and additional signals for production testing and scan isolation are connected.
The open-source version leaves `lc_nvm_debug_en` from `lc_ctrl` unused.

The interface to the RRAM controller (`rram_macro_req_t`/`rram_macro_rsp_t`) is described in [RRAM Controller - Macro Interface](../rram_ctrl/README.md#rram-controller---macro-interface).
The macro contains a CSR block for vendor specific operations which is not used in the open-source version.

## Markers

During its init after reset, the macro reads two markers from INFO page `MarkerInfoPage` (4) and latches them until the next reset.
The markers support the RRAM forming and the CP flow.
They are read in every life cycle state, independent of the memory protection in `rram_ctrl`.

| Marker | Word offset | Set if |
| --- | --- | --- |
| `DIS_VOL_RAW_UNLOCK` | `DisVolRawUnlockWords` (0) | the word holds exactly `MarkerMagic`, zero-extended to 128 bits and XORed with the bus word addresses like `rram_ctrl` writes it, with clean ECC |
| `CP_DONE` | `CpDoneWords` (1) | the word holds exactly `MarkerMagic`, zero-extended to 128 bits and XORed with the bus word addresses like `rram_ctrl` writes it, with clean ECC |

The markers are always read with ECC, and they are not scrambled.
A read with an ECC error or any other value means "not set", so a blank or unformed array reads as "not set".
`MarkerMagic` is the public 16-bit constant `MuBi16True` (`16'h9696`), since the CP flow has to write it.
It has 8 1-bits (`MarkerMagicMinWeight`), so a marker only falls back to "not set" if all of them decay to zero.
Both markers use the same value, since each marker has its own words.

The decoded markers drive two MuBi8 outputs:

- `allow_vol_unlock_o` is True unless `DIS_VOL_RAW_UNLOCK` is set.
- `cp_done_o` is True if `CP_DONE` is set, and False otherwise.
- Both outputs are an invalid MuBi8 value until the markers are latched.

Each marker has one copy for now, and it is read once.
The parameters (`NumMarkerCopies` and the word lists in `rram_ctrl_pkg`) allow more copies later, and a later version could confirm the result in a second read before the markers are latched.

The macro does not protect the marker page itself.
`rram_ctrl` only allows writes to it while `lc_nvm_debug_en` is On.
Newly written markers only take effect after the next reset.

## Zero View

While `DIS_VOL_RAW_UNLOCK` is not set, `rram_ctrl` must not see the content of the array.
This is the case during the forming flow, where the part is only volatilely unlocked.
The zero view is off only while `allow_vol_unlock_o` is strictly `MuBi8False`, so it also stays on for an invalid value.

| Request from `rram_ctrl` | Zero view on | Zero view off |
| --- | --- | --- |
| Read outside of the marker page | returns 0 with clean ECC, without accessing the array | normal |
| Write outside of the marker page | dropped, completes with `err` | normal |
| Read or write of the marker page | normal | normal |

So `otp_ctrl` sees an all-zero OTP image, the life cycle partition decodes as `RAW` with counter 0, and any OTP write fails.
The marker page is exempt, so the CP flow can write `DIS_VOL_RAW_UNLOCK` and read it back.
The marker read during init, the vendor-specific JTAG/BIST access and the TRC's own reads are not affected.

## Simulation Notes

The model does not initialize its arrays itself.
Without the `DIS_VOL_RAW_UNLOCK` marker, the zero view is on and all OTP content reads as zero.
So each environment loads the INFO array of a formed part:

- The chip-level DV clears the INFO array and writes the marker through the backdoor (`preload_rram_markers()`).
- The `rram_ctrl` block DV writes the marker in its testbench.
- Verilator and FPGA load the INFO image from `gen-rram-img.py --out-info-vmem`, which sets the marker for every life cycle state except `RAW`.

In DV, tests of the forming flow and the volatile RAW unlock pass `+rram_dis_vol_raw_unlock=0` to skip the marker, which turns the zero view on.

## Replacing the macro

`rram_macro` is a FuseSoC virtual core (`lowrisc:virtual_ip:rram_macro`): this open-source implementation is the default, and a partner can map the virtual core to their own implementation instead, without changing anything outside `rram_macro` itself.
Since `earlgrey_pd_main.sv` instantiates `rram_macro` with a fixed parameter and port list, a replacement must match the open-source model exactly.


## Simulation

A pre-dv environment exists that allows to perform basic read and write transactions to the RRAM macro.
It can be started with dvsim:

`./util/dvsim/dvsim.py hw/ip/rram_macro/pre_dv/rram_macro_sim_cfg.hjson -i smoke`
