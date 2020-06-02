# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

BORING_SSL_PATH=../boringssl

NAME=aes_example aes_modes
FLAGS=-Wall -O2 -g

ifneq ($(wildcard $(BORING_SSL_PATH)/build/crypto/libcrypto.a),)
	FLAGS+=-DUSE_BORING_SSL
endif

all:
	@for f in $(NAME) ; do \
		gcc $(FLAGS) crypto.c aes.c $${f}.c -o $${f} -I$(BORING_SSL_PATH) -L$(BORING_SSL_PATH)/build/crypto -lcrypto -lpthread ; \
	done

clean:
	rm -f $(NAME)
