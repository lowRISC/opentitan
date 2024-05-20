#!/bin/sh
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

g++ -Wall -Werror -std=c++14 -c -o suspend_test.o -DSTREAMTEST_LIBUSB=1 -I../usbdev_stream suspend_test.cc
g++ -Wall -Werror -std=c++14 -c -o usb_device.o -DSTREAMTEST_LIBUSB=1 ../usbdev_stream/usb_device.cc

g++ -g -O2 -o suspend_test suspend_test.o usb_device.o -lusb-1.0
