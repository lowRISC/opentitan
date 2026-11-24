% if macro_backend == "rram_ctrl":
This top uses `rram_ctrl` as the backend.
The OTP partitions are stored in a reserved OTP region at the top of the RRAM data partition, which is inaccessible to software (see the [OTP Hardware Plug](../../../../ip/rram_ctrl/doc/theory_of_operation.md#otp-hardware-plug) of `rram_ctrl`).
There are no vendor-specific OTP programming smoke checks, and the vendor test signals of the life cycle controller are not connected.
% elif macro_backend == "otp_macro":
This top uses `otp_macro` as the backend.
The vendor test signals of the life cycle controller, as well as the TL-UL test interface, power sequencing and observability signals, connect to `otp_macro`.
Test access to the OTP is therefore only possible via the TL-UL test interface of `otp_macro`, which is gated with `lc_dft_en`.
The silicon creator may implement OTP programming smoke checks on the VENDOR_TEST partition inside the proprietary version of `otp_macro`.
% else:
This top uses `${macro_backend}` as the backend.
% endif
