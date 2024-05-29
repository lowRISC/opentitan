#!/bin/sh
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

g++ -Wall -Werror -std=c++14 -c -o stream_test.o -DSTREAMTEST_LIBUSB=1 stream_test.cc
g++ -Wall -Werror -std=c++14 -c -o usbdev_iso.o -DSTREAMTEST_LIBUSB=1 usbdev_iso.cc
g++ -Wall -Werror -std=c++14 -c -o usbdev_int.o -DSTREAMTEST_LIBUSB=1 usbdev_int.cc
g++ -Wall -Werror -std=c++14 -c -o usbdev_serial.o -DSTREAMTEST_LIBUSB=1 usbdev_serial.cc
g++ -Wall -Werror -std=c++14 -c -o usbdev_stream.o -DSTREAMTEST_LIBUSB=1 usbdev_stream.cc
g++ -Wall -Werror -std=c++14 -c -o usbdev_utils.o -DSTREAMTEST_LIBUSB=1 usbdev_utils.cc
g++ -Wall -Werror -std=c++14 -c -o usb_device.o -DSTREAMTEST_LIBUSB=1 usb_device.cc

g++ -g -O2 -o stream_test stream_test.o usbdev_iso.o usbdev_int.o usbdev_serial.o usbdev_stream.o usbdev_utils.o usb_device.o -lusb-1.0
