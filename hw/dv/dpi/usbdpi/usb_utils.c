// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "usb_utils.h"

#include <stdio.h>
#include <stdlib.h>

static const char *pid_names[] = {
    "Rsvd",     //         0000b
    "OUT",      //         0001b
    "ACK",      //         0010b
    "DATA0",    //         0011b
    "PING",     //         0100b
    "SOF",      //         0101b
    "NYET",     //         0110b
    "DATA2",    //         0111b
    "SPLIT",    //         1000b
    "IN",       //         1001b
    "NAK",      //         1010b
    "DATA1",    //         1011b
    "PRE/ERR",  //         1100b
    "SETUP",    //         1101b
    "STALL",    //         1110b
    "MDATA"     //         1111b
};

// Decode a PID and return its textual name, iff valid
const char *decode_pid(uint8_t pid) {
  // Valid PIDs are formed from two complementary nibbles
  return (((pid ^ 0xf0u) >> 4) ^ (pid & 0xfu)) ? "???" : pid_names[pid & 0xfu];
}

// Dump a sequence of bytes as hexadecimal and AsCII for diagnostic purposes
void dump_bytes(FILE *out, const char *prefix, const uint8_t *data, size_t n,
                uint32_t flags) {
  static const char hex_digits[] = "0123456789abcdef";
  const unsigned ncols = 0x10u;
  char buf[ncols * 4u + 2u];

  if (!prefix) {
    prefix = "";
  }

  // Note: we have no generic printf functionality and must use LOG_INFO()
  while (n > 0u) {
    const unsigned chunk = (n > ncols) ? ncols : (unsigned)n;
    const uint8_t *row = data;
    unsigned idx = 0u;
    char *dp = buf;

    // Columns of hexadecimal bytes
    while (idx < chunk) {
      dp[0] = hex_digits[row[idx] >> 4];
      dp[1] = hex_digits[row[idx++] & 0xfu];
      dp[2] = ' ';
      dp += 3;
    }
    while (idx++ < ncols) {
      dp[2] = dp[1] = dp[0] = ' ';
      dp += 3;
    }

    // Printable ASCII characters
    for (unsigned idx = 0u; idx < chunk; idx++) {
      char ch = row[idx];
      *dp++ = (ch < ' ' || ch >= 0x7f) ? '.' : ch;
    }
    *dp = '\0';
    fprintf(out, "%s%s\n", prefix, buf);
    data += chunk;
    n -= chunk;
  }
}

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern uint16_t get_le16(const uint8_t *dp);
extern uint32_t get_le32(const uint8_t *dp);
extern uint8_t *set_le16(uint8_t *dp, uint16_t n);
extern uint8_t *set_le32(uint8_t *dp, uint32_t n);
