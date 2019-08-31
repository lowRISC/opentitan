//******************************************************************************
//
// CRC5() - Computes a USB CRC5 value given an input value.
//          Ported from the Perl routine from the USB white paper entitled
//          "CYCLIC REDUNDANCY CHECKS IN USB"
//          www.usb.org/developers/whitepapers/crcdes.pdf
//
//          Ported by Ron Hemphill 01/20/06.
//
//  dwinput:    The input value.
//  iBitcnt:    The number of bits represented in dwInput.
//
//  Returns:    The computed CRC5 value.
//
//  Examples (from the white paper):
//      dwInput     iBitcnt     Returns:
//      0x547       11          0x17
//      0x2e5       11          0x1C
//      0x072       11          0x0E
//      0x400       11          0x17
//
//******************************************************************************
#include <stdint.h>
#ifndef TESTING_CRC
#include "usbdpi.h"
#endif

#define INT_SIZE 32  // Assumes 32-bit integer size
uint32_t CRC5_MSBfirst(uint32_t dwInput, int iBitcnt) {
  const uint32_t poly5 = (0x05 << (INT_SIZE - 5));
  uint32_t crc5 = (0x1f << (INT_SIZE - 5));
  uint32_t udata = (dwInput << (INT_SIZE - iBitcnt));

  if ((iBitcnt < 1) || (iBitcnt > INT_SIZE)) {  // Validate iBitcnt
    return 0xffffffff;
  }

  while (iBitcnt--) {
    if ((udata ^ crc5) & (0x1 << (INT_SIZE - 1))) {  // bit4 != bit4?
      crc5 <<= 1;
      crc5 ^= poly5;
    } else {
      crc5 <<= 1;
    }

    udata <<= 1;
  }

  // Shift back into position
  crc5 >>= (INT_SIZE - 5);

  // Invert contents to generate crc field
  crc5 ^= 0x1f;

  return crc5;
}  // CRC5()

/* This is the little endian version, so you can feed an 11 bit data
 * value and get back 5 bits to OR in to the top to construct 16 bits
 *
 * Adapted by mdhayter
 */

uint32_t CRC5(uint32_t dwInput, int iBitcnt) {
  const uint32_t poly5 = 0x14;
  uint32_t crc5 = 0x1f;
  uint32_t udata = dwInput;

  if ((iBitcnt < 1) || (iBitcnt > INT_SIZE)) {  // Validate iBitcnt
    return 0xffffffff;
  }

  while (iBitcnt--) {
    if ((udata ^ crc5) & 0x01) {
      crc5 >>= 1;
      crc5 ^= poly5;
    } else {
      crc5 >>= 1;
    }

    udata >>= 1;
  }

  // Invert contents to generate crc field
  crc5 ^= 0x1f;

  return crc5;
}  // CRC5()

// Added mdhayter
uint32_t CRC16(uint8_t *data, int bytes) {
  const uint32_t poly16 = 0xA001;
  uint32_t crc16 = 0xffff;
  int i;

  for (i = 0; i < bytes; i++) {
    uint32_t udata = data[i];
    int bit = 8;

    while (bit--) {
      if ((udata ^ crc16) & 0x01) {
        crc16 >>= 1;
        crc16 ^= poly16;
      } else {
        crc16 >>= 1;
      }

      udata >>= 1;
    }
  }
  // Invert contents to generate crc field
  crc16 ^= 0xffff;

  return crc16;
}  // CRC16()
