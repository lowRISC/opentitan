This top uses `rram_ctrl` as the backend.
The OTP partitions are stored in a reserved OTP region at the top of the RRAM data partition, which is inaccessible to software (see the [OTP Hardware Plug](../../../../ip/rram_ctrl/doc/theory_of_operation.md#otp-hardware-plug) of `rram_ctrl`).
There are no vendor-specific OTP programming smoke checks, and the vendor test signals of the life cycle controller are not connected.
