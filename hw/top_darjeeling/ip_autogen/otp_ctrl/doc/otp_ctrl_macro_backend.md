This top uses `otp_macro` as the backend.
The vendor test signals of the life cycle controller, as well as the TL-UL test interface, power sequencing and observability signals, connect to `otp_macro`.
Test access to the OTP is therefore only possible via the TL-UL test interface of `otp_macro`, which is gated with `lc_dft_en`.
The silicon creator may implement OTP programming smoke checks on the VENDOR_TEST partition inside the proprietary version of `otp_macro`.
