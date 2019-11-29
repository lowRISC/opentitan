# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

PROGRAM ?= spiflash
PROGRAM_CFLAGS = -Wall -g -Os

MPSSE_DIR = ../vendor/mpsse
MPSSE_OBJS = $(MPSSE_DIR)/mpsse.o $(MPSSE_DIR)/support.o

INC += -I../../.. # i.e., $REPO_TOP.
CFLAGS += $(INC) -std=c99
CXXFLAGS += $(INC) -Wall -std=c++14
LDFLAGS += -lcrypto -lftdi1 -lusb-1.0 -L/usr/lib/x86_64-linux-gnu
DEPS  = spi_interface.h updater.h verilator_spi_interface.h ftdi_spi_interface.h
OBJS := verilator_spi_interface.o updater.o ftdi_spi_interface.o

all: $(PROGRAM)

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.o: %.cc $(DEPS)
	$(CXX) $(CXXFLAGS) -c -o $@ $<

$(PROGRAM): $(PROGRAM).cc $(OBJS) $(MPSSE_OBJS)
	$(CXX) $(CXXFLAGS) spiflash.cc -o spiflash $(DEPS) $(OBJS) $(MPSSE_OBJS) $(LDFLAGS)

clean:
	rm -f $(PROGRAM) *.o ${MPSSE_OBJS}
