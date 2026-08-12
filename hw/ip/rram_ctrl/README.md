# RRAM CTRL HWIP Technical Specification

# Overview

This document specifies the RRAM Controller hardware IP functionality.
The RRAM Controller is a comportable IP that controls the RRAM macro.
This block can be connected to the bus system, and offers similar functionality to the Flash Controller.
It must be used in conjunction with the RRAM Macro and cannot be used standalone.

## Features

The RRAM Controller supports read, and write commands to the RRAM macro.
It has two TL-UL interfaces. `tl_core` is used to access the register bank and the FIFOs and `tl_host` is a read-only interface to access data stored in the RRAM.
The RRAM Controller interacts with several other hardware IPs such as the life cycle controller, OTP controller, and key manager.

## OTP

RRAM supports emulated OTP by mapping the functionality of `otp_macro` to the RRAM Controller.
`rram_ctrl_otp.sv` implements the `otp_ctrl_macro_pkg` interface `otp_ctrl` expects (the same
interface a standalone `otp_macro` would implement), emulating OTP's read-set-write semantics on
top of the RRAM array underneath.

### Page layout

Of the RRAM data array's `TotalDataPages` (4096) pages, the last `OtpPages` (5) are reserved for
OTP.

- Page `OtpStartPage` (4091): the integrity page — one 8-bit Hamming(72,64) syndrome per 64-bit
  chunk of OTP data, described below.
- Pages `OtpStartPage + 1` through `TotalDataPages - 1` (4092-4095): OTP data itself.

`OtpStartAddr`/`OtpIntgStartAddr` (`rram_ctrl_otp.sv`) give the byte addresses of the data and
integrity regions respectively, both computed from `OtpStartPage`.

### Integrity scheme

Every OTP word gets two independent layers of protection: the RRAM macro's own ECC, same as every
other word in the array, for physical storage reliability; and, on top of that, one 8-bit
Hamming(72,64) syndrome per 64 bits of OTP data (`prim_secded_hamming_72_64_enc`), stored
separately in the integrity page at the offset corresponding to that data's position. The latter is
OTP-specific and mirrors real OTP hardware's own integrity mechanism. `*Raw` OTP commands
(`ReadRaw`/`WriteRaw`) bypass only this second, OTP-specific check, matching real OTP hardware's
raw access mode — the RRAM macro's own ECC still applies underneath regardless.

### Where this is implemented

- `rram_ctrl_otp.sv`: Every front-door OTP read/write goes through this hardware module. It
  implements the read-set-write FSM and the integrity check/rewrite logic described above.
- `util/design/gen-rram-img.py`: Generates an OTP image with the integrity syndromes already
  appended (`--out-otp-vmem`). This image can be used to backdoor-load OTP content directly, on the
  FPGA or in simulation.
- `hw/ip/rram_ctrl/dv/bkdr/rram_ctrl_otp_bkdr_util.sv`: DV's own backdoor-load/inject-errors
  utility, which can also append the integrity syndromes itself, and cross-checks its computation
  against `gen-rram-img.py`'s in `load_mem_from_file()`.
