// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>
#include <stdlib.h>

#define TESTING_CRC
#include "usb_crc.c"

unsigned char buf[1024];

int main(int argc, char *argv[]) {
  int i;
  int base;
  if (argv[1][0] != '-') {
    int val = strtol(argv[1], NULL, 0);
    int crc = CRC5(val, 11);
    printf("CRC5(0x%x, 11) -> 0x%x (CRC << 3 is 0x%02x, Combined 0x%04x)\n",
           val, crc, crc << 3, crc << 11 | val);
    exit(0);
  }
  if (argv[1][1] == 'x') {
    base = 16;
  } else {
    base = 0;
  }
  for (i = 2; i < argc; i++) {
    buf[i - 2] = strtol(argv[i], NULL, base);
    printf("%02x ", buf[i - 2]);
  }
  printf("CRC16 = 0x%04x\n", CRC16(buf, argc - 2));
}

/*
Working up USB app note page 5
mdh10@homer:usbdpi$ ./a.out 0x1
CRC5(0x1, 11) -> 0x1d
mdh10@homer:usbdpi$ ./a.out 0x270
CRC5(0x270, 11) -> 0xe
mdh10@homer:usbdpi$ ./a.out 0x53a
CRC5(0x53a, 11) -> 0x7
mdh10@homer:usbdpi$ ./a.out 0x715
CRC5(0x715, 11) -> 0x1d
mdh10@homer:usbdpi$ ./a.out 0x710

 */
