// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/xmodem.h"

#ifndef XMODEM_TESTLIB
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#else
#include "sw/device/silicon_creator/lib/xmodem_testlib.h"
#endif

/**
 * Constants used in the XModem-CRC protocol.
 */
enum {
  kXModemCrc16 = 0x43,
  kXModemSoh = 0x01,
  kXModemStx = 0x02,
  kXModemEof = 0x04,
  kXModemAck = 0x06,
  kXModemNak = 0x15,
  kXModemCancel = 0x18,
  kXModemPoly = 0x1021,
  kXModemSendRetries = 3,
  kXModemMaxErrors = 2,
  kXModemShortTimeout = 100,
  kXModemLongTimeout = 1000,
};

#ifndef XMODEM_TESTLIB
size_t xmodem_read(void *iohandle, uint8_t *data, size_t len,
                   uint32_t timeout_ms) {
  (void)iohandle;
  return uart_read(data, len, timeout_ms);
}

void xmodem_write(void *iohandle, const uint8_t *data, size_t len) {
  (void)iohandle;
  uart_write(data, len);
}
#endif

void xmodem_putchar(void *iohandle, uint8_t ch) {
  xmodem_write(iohandle, &ch, sizeof(ch));
}

/**
 * Calculates a CRC-16 using the XModem polynomial.
 */
static uint16_t crc16(uint16_t crc, const void *buf, size_t len) {
  const uint8_t *p = (const uint8_t *)buf;
  for (size_t i = 0; i < len; ++i, ++p) {
    crc ^= *p << 8;
    for (size_t j = 0; j < 8; ++j) {
      bool msb = (crc & 0x8000) != 0;
      crc <<= 1;
      if (msb)
        crc ^= kXModemPoly;
    }
  }
  return crc;
}

/**
 * Calculate an XModem CRC16 for a to-be-transmitted block.
 */
static uint16_t crc16_block(const void *buf, size_t len, size_t block_sz) {
  uint16_t crc = crc16(0, buf, len);
  uint8_t pad = 0;
  for (; len < block_sz; ++len) {
    crc = crc16(crc, &pad, 1);
  }
  return crc;
}

void xmodem_recv_start(void *iohandle) {
  xmodem_putchar(iohandle, kXModemCrc16);
}

void xmodem_ack(void *iohandle, bool ack) {
  xmodem_putchar(iohandle, ack ? kXModemAck : kXModemNak);
}

rom_error_t xmodem_recv_frame(void *iohandle, uint32_t frame, uint8_t *data,
                              size_t *rxlen, uint8_t *unknown_rx) {
  uint8_t ch;
  size_t n = xmodem_read(iohandle, &ch, sizeof(ch), kXModemLongTimeout);
  if (n == 0) {
    return kErrorXModemTimeoutStart;
  } else if (ch == kXModemStx || ch == kXModemSoh) {
    // Determine if we should expect a 1K or 128 byte block.
    size_t len = ch == kXModemStx ? 1024 : 128;
    uint8_t pkt[2];

    // Get the frame number and its inverse.
    n = xmodem_read(iohandle, pkt, sizeof(pkt), kXModemShortTimeout);
    if (n != sizeof(pkt)) {
      return kErrorXModemTimeoutPacket;
    }

    // If the frame or its inverse are incorrect, cancel.
    bool cancel = pkt[0] != (uint8_t)frame || pkt[0] != 255 - pkt[1];

    // Receive the data.  At 115200 bps, 1K should take about 89ms to
    // receive a 1K frame.  A short timeout should be enough, but we'll
    // be generous and give more time.
    n = xmodem_read(iohandle, data, len, kXModemShortTimeout * 3);
    if (n != len) {
      return kErrorXModemTimeoutData;
    }

    // Receive the CRC-16 from the client.
    n = xmodem_read(iohandle, pkt, sizeof(pkt), kXModemShortTimeout);
    if (n != sizeof(pkt)) {
      return kErrorXModemTimeoutCrc;
    }
    if (cancel) {
      xmodem_cancel(iohandle);
      return kErrorXModemCancel;
    }

    // Compute our own CRC-16 and compare with the client's value.
    uint16_t crc = (uint16_t)(pkt[0] << 8 | pkt[1]);
    uint16_t val = crc16(0, data, len);
    if (crc != val) {
      return kErrorXModemCrc;
    }
    if (rxlen)
      *rxlen = len;
    return kErrorOk;
  } else if (ch == kXModemEof) {
    return kErrorXModemEndOfFile;
  } else {
    if (unknown_rx)
      *unknown_rx = (uint8_t)ch;
    return kErrorXModemUnknown;
  }
}

/**
 * Wait for the xmodem-crc start sequence.
 */
static rom_error_t xmodem_send_start(void *iohandle, uint32_t retries) {
  uint8_t ch;
  int cancels = 0;
  for (uint32_t i = 0; i < retries; ++i) {
    size_t n = xmodem_read(iohandle, &ch, sizeof(ch), kXModemLongTimeout);
    if (n == 0)
      continue;
    switch (ch) {
      case kXModemCrc16:
        return kErrorOk;
      case kXModemNak:
        return kErrorXModemProtocol;
      case kXModemCancel:
        cancels += 1;
        if (cancels >= 2)
          return kErrorXModemCancel;
        break;
      default:
          /* Unknown character: do nothing */
          ;
    }
  }
  return kErrorXModemTimeoutStart;
}

void xmodem_cancel(void *iohandle) {
  xmodem_putchar(iohandle, kXModemCancel);
  xmodem_putchar(iohandle, kXModemCancel);
}

static rom_error_t xmodem_send_finish(void *iohandle) {
  xmodem_putchar(iohandle, kXModemEof);
  uint8_t ch;
  xmodem_read(iohandle, &ch, sizeof(ch), kXModemLongTimeout);
  if (ch != kXModemAck) {
    // Should have seen an ACK, but we don't really care since there is nothing
    // we could do about it.
  }
  return kErrorOk;
}

static rom_error_t xmodem_send_data(void *iohandle, const void *data,
                                    size_t len, uint32_t max_errors) {
  const uint8_t *p = (const uint8_t *)data;
  uint32_t block = 0;
  uint32_t errors = 0;
  uint32_t cancels = 0;
  while (len) {
    uint32_t block_sz = len < 1024 ? 128 : 1024;
    uint32_t chunk = len < block_sz ? len : block_sz;
    block += 1;

    uint16_t crc = crc16_block(p, chunk, block_sz);
    while (true) {
      // Start an XModem-CRC frame according to size.
      // XModem-CRC supports both 128-byte and 1K frames.
      // Write the header: <Soh or Stx> <block> <inverse-of-block>
      xmodem_putchar(iohandle, block_sz == 128 ? kXModemSoh : kXModemStx);
      xmodem_putchar(iohandle, (uint8_t)block);
      xmodem_putchar(iohandle, 255 - (uint8_t)block);
      // Write the data.
      xmodem_write(iohandle, p, chunk);
      // Pad the block out to the block size.
      for (uint32_t i = chunk; i < block_sz; ++i) {
        xmodem_putchar(iohandle, 0);
      }
      // Write the CRC16 value.
      xmodem_putchar(iohandle, crc >> 8);
      xmodem_putchar(iohandle, crc & 0xFF);

      // Get and check the ACK.
      uint8_t ch;
      size_t n = xmodem_read(iohandle, &ch, sizeof(ch), kXModemLongTimeout);
      if (n == 0)
        return kErrorXModemTimeoutAck;
      switch (ch) {
        case kXModemAck:
          goto next_block;
        case kXModemCancel:
          cancels += 1;
          if (cancels >= 2)
            return kErrorXModemCancel;
          break;
        case kXModemNak:
        default:
          errors += 1;
          break;
      }
      if (errors >= max_errors) {
        return kErrorXModemTooManyErrors;
      }
    }
  next_block:
    p += chunk;
    len -= chunk;
  }
  return kErrorOk;
}

rom_error_t xmodem_send(void *iohandle, const void *data, size_t len) {
  HARDENED_RETURN_IF_ERROR(xmodem_send_start(iohandle, 30));
  HARDENED_RETURN_IF_ERROR(
      xmodem_send_data(iohandle, data, len, kXModemMaxErrors));
  HARDENED_RETURN_IF_ERROR(xmodem_send_finish(iohandle));
  return kErrorOk;
}
