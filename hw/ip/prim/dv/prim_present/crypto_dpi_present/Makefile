# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

all: crypto_present.so

crypto_present.so: crypto_present.c
	@echo "[build]: build crypto_present.so library for python to use C"
	gcc -o crypto_present.so -shared -fPIC -O2 crypto_present.c

clean:
	rm -rf crypto_present.so
