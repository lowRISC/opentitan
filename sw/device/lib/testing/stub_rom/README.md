# Stub ROM

This directory contains the code of a stub ROM.
Its purpose is to a build a minimal but valid ROM which is inserted into the FPGA bitstream.
This stub ROM simply loops while calling `wfi`.
The benefit is to reduce the dependency of the bitstream to an extremely small subset of software files, hence avoiding useless bitstream rebuild in CI.
Having a valid ROM is preferable to filling the ROM with zeroes or random data since it guarantees that ROM data is valid and the chip can boot, avoiding alerts with potential escalations.
