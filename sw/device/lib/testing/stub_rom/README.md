# Stub ROM

This directory contains the code of a stub ROM.
Its purpose is to a build a minimal but valid ROM which is inserted into the FPGA bitstream.
This stub ROM simply loops while calling `wfi`.
The benefit is to reduce the dependency of the bitstream to an extremely small subset of software files, hence avoiding useless bitstream rebuild in CI.
