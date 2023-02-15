// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_STREAM_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_STREAM_H_
#include <cstddef>
#include <cstdint>
#include <sys/types.h>

/**
 * States in reception of signature state
 */
typedef enum {
  kSigStateStart = 0,
  kSigStateCheckHead,
  kSigStateSkipBody,
  kSigStateCheckTail,
  // Signature has been correctly received
  kSigStateReceived,
} sig_state_t;

/**
 * Stream signature
 * Note: this needs to be transferred over a byte stream
 */
typedef struct __attribute__((packed)) usbdev_stream_sig {
  /**
   * Head signature word
   */
  uint32_t head_sig;
  /**
   * Initial value of LFSR
   */
  uint8_t init_lfsr;
  /**
   * Stream number
   */
  uint8_t stream;
  /**
   * Reserved fields; should be zero
   */
  uint8_t reserved1;
  uint8_t reserved2;
  /**
   * Number of bytes to be transferred
   */
  uint32_t num_bytes;
  /**
   * Tail signature word
   */
  uint32_t tail_sig;
} usbdev_stream_sig_t;

// Data stream
class USBDevStream {
 public:
  /**
   * Open the stream using the given port names
   *
   * @param  id        Stream IDentifier
   * @param  in_name   Name of input port to use
   * @param  out_name  Name of output port to use
   * @paran  num_bytes Number of bytes to be transferred
   */
  bool Open(unsigned id, const char *in_name, const char *out_name,
            uint32_t num_bytes);
  /**
   * Finalise the stream, releasing all resources
   */
  void Close();

  /**
   * Service this stream
   *
   * @return         true iff test should continue, false indicates error
   */
  bool Service();

  /**
   * Indicates whether this stream has completed its transfer
   *
   * @return         true iff this stream has nothing more to do
   */
  bool Completed() const;

  /**
   * Returns the total number of bytes to be transferred by this stream
   *
   * @param          Number of bytes to be transferred
   */
  uint32_t TransferBytes() const { return transfer_bytes_; }

  /**
   * Returns a count of the number of bytes sent to the device
   *
   * @return         Number of bytes sent
   */
  uint32_t BytesSent() const { return bytes_sent_; }

 private:
  /**
   * Size of circular buffer used for streaming
   */
  static constexpr uint32_t kBufferSize = 0x100000U;

  // Utility function for collecting a byte from the stream signature, handling
  // wrap around at the end of the circular buffer
  inline uint8_t sig_read8(size_t offset) {
    unsigned rd_idx = buf_.rd_idx + offset;
    if (rd_idx >= kBufferSize) {
      rd_idx -= kBufferSize;
    }
    return buf_.data[rd_idx];
  }

  // Utility function for collecting a 32-bit word from the stream signature,
  // handling wrap around at the end of the circular buffer
  inline uint32_t sig_read32(size_t offset) {
    unsigned rd_idx = buf_.rd_idx + offset;
    unsigned n = 4U;
    uint32_t d = 0U;
    while (n-- > 0U) {
      if (rd_idx >= kBufferSize) {
        rd_idx -= kBufferSize;
      }
      // Transmission of multi-byte value is little endian
      d = (d >> 8) | (buf_.data[rd_idx++] << 24);
    }
    return d;
  }

  // Detect a stream signature within the byte stream;
  ssize_t sig_detect(ssize_t nrecv);

  /**
   * Stream IDentifier
   */
  unsigned id_;
  /**
   * Input port handle
   */
  int in_;
  /**
   * Output port handle
   */
  int out_;
  /**
   * Input port name
   */
  //  char in_name[FILENAME_MAX];
  /**
   * Output port name
   */
  //  char out_name[FILENAME_MAX];
  /**
   * Have we received the stream signature yet?
   */
  sig_state_t sig_recvd_;
  unsigned sig_cnt_;
  /**
   * Total number of bytes received
   */
  uint32_t bytes_recvd_;
  /**
   * Total number of bytes sent
   */
  uint32_t bytes_sent_;
  /**
   * Device-side LFSR; byte stream expected from usbdev_stream_test
   */
  uint8_t tst_lfsr_;
  /**
   * Host/DPI-side LFSR
   */
  uint8_t dpi_lfsr_;
  /**
   * Number of bytes to be transferred
   */
  uint32_t transfer_bytes_;
  /**
   * Circular buffer of streamed data
   */
  struct {
    /**
     * Offset at which to write the next received data (IN from device)
     */
    uint32_t wr_idx;
    /**
     * Offset of next byte to be read from the buffer (OUT to device)
     */
    uint32_t rd_idx;
    /**
     * Circular buffer of data being transferred from input to output port
     */
    uint8_t data[kBufferSize];
  } buf_;
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_STREAM_H_
