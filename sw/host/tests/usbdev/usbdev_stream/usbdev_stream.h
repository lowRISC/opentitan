// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_STREAM_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_STREAM_H_
#include <cstddef>
#include <cstdint>
#include <string>
#include <sys/types.h>

// TODO: Move the states into the class, along with the transfer types probably.

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

// Test/stream flags
typedef enum {
  /**
   * Mask for extracting the stream ID number
   */
  kUsbdevStreamFlagID = 0x0FU,
  /**
   * Host shall retrieve IN data from the device for this stream
   */
  kUsbdevStreamFlagRetrieve = 0x10U,
  /**
   * Host shall check that IN data matches as expected
   */
  kUsbdevStreamFlagCheck = 0x20U,
  /**
   * DPI model (or Host) shall retry IN data fetches, where possible
   */
  kUsbdevStreamFlagRetry = 0x40U,
  /**
   * Host shall send OUT data to the device for this stream
   */
  kUsbdevStreamFlagSend = 0x80U
} usbdev_stream_flags_t;

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
   * Note: for Isochronous Transfers, this is the initial value of the sender's
   *       LFSR for _this packet_
   */
  uint8_t init_lfsr;
  /**
   * Stream number and flags
   */
  uint8_t stream;
  /**
   * Sequence number, low part; for non-Isochronous streams this will always be
   * zero because a signature is used only at the start of the data stream.
   */
  uint8_t seq_lo;
  /**
   * Sequence number, high part; for non-Isochronous streams this will always be
   * zero because a signature is used only at the start of the data stream.
   */
  uint8_t seq_hi;
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
  USBDevStream(unsigned id, uint32_t num_bytes, bool retrieve, bool check,
               bool send, bool verbose);
  virtual ~USBDevStream() {}

  /**
   * Open the stream using the given port names
   *
   * @param  id        Stream IDentifier
   * @param  in_name   Name of input port to use
   * @param  out_name  Name of output port to use
   * @paran  num_bytes Number of bytes to be transferred
   * @param  retrieve  Retrieve IN data for this stream?
   * @param  check     Check retrieved data?
   * @param  send      Send OUT data for this stream
   */
  bool Open(unsigned id, const char *in_name, const char *out_name,
            uint32_t num_bytes, bool retrieve, bool check, bool send);
  /**
   * Finalise the stream, releasing all resources
   */
  virtual void Close() = 0;
  /**
   * Return the Stream IDentifier of this stream.
   */
  unsigned ID() const { return id_; }
  /**
   * Return a Stream IDentifier prefix suitable for logging/reporting.
   */
  std::string PrefixID() {
    std::string s("S");
    s += std::to_string(id_);
    s += ": ";
    return s;
  }
  /**
   * Set Stream IDentifier and flags
   */
  void SetProperties(unsigned id, bool retrieve, bool check, bool send) {
    id_ = id;
    retrieve_ = retrieve;
    check_ = check;
    send_ = send;
  }
  /**
   * Service this stream
   *
   * @return         true iff test should continue, false indicates error
   */
  virtual bool Service();
  /**
   * Indicates whether this stream has completed its transfer
   *
   * @return         true iff this stream has nothing more to do
   */
  virtual bool Completed() const;
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

 protected:
  /**
   * Returns the amount of contiguous space available, in bytes.
   */
  uint32_t SpaceAvailable(uint8_t **space, bool contig);
  /**
   *
   */
  bool AddData(const uint8_t *data, uint32_t len);
  /**
   *
   */
  bool CommitData(uint32_t len) { return AddData(nullptr, len); }
  /**
   * CLear the circular buffer by removing all of its contained data bytes.
   *
   * Note: this is achieved by advancing the read index to match the current
   * write index, so all committed/added data is discarded, by any write data
   * that has only been provisioned at this point does remain valid and may
   * still be committed subsequently.
   */
  void ClearBuffer();
  /**
   *
   */
  void SigReset() {
    sig_recvd_ = kSigStateStart;
    sig_cnt_ = 0U;
  }
  /**
   *
   */
  bool SigReceived() const { return (sig_recvd_ == kSigStateReceived); }

  /**
   *
   */
  void SigProcess(const usbdev_stream_sig_t &sig);
  /**
   * Detect and parse stream/packet signature,
   * returning a count of the number of bytes to be discarded from the start
   * of this data. Usually this is zero, but if a valid stream signature is
   * required, bytes must be discarded until the signature is received.
   */
  uint32_t SigDetect(usbdev_stream_sig_t *sig, const uint8_t *sp,
                     uint32_t nrecv);
  /**
   *
   */
  void SigReport(const usbdev_stream_sig_t &sig);

  /**
   *
   */
  /**
   * Generate a sequence of bytes _as if_ we'd received them correctly from the
   * device.
   */
  void GenerateData(uint8_t *dp, uint32_t len);
  /**
   * Process the given sequence of bytes according to the current stream state
   */
  bool ProcessData(uint8_t *dp, uint32_t len);
  /**
   * Return the number of contiguous bytes of data available in the stream
   * buffer, and a pointer to the first byte of data. This may be fewer than the
   * total number of bytes in the buffer, if the data wraps at the end of the
   * circular buffer.
   *
   * @param  data   Receives the pointer to the first data byte.
   * @return The number of contiguous data bytes available.
   */
  uint32_t DataAvailable(uint8_t **data, bool contig);
  /**
   * Update the stream buffer to indicate that data has been consumed.
   *
   * @param  len    Number of bytes of data consumed.
   * @return true iff the buffer was successfully updated.
   */
  bool ConsumeData(uint32_t len);

  /**
   * Size of circular buffer used for streaming
   */
  static constexpr uint32_t kBufferSize = 0x100000U;

  // Utility function for collecting a byte from the stream signature, handling
  // wrap around at the end of the circular buffer
  inline uint8_t sig_read8(size_t offset) {
    uint32_t rd_idx = buf_.rd_idx + offset;
    if (rd_idx >= kBufferSize) {
      rd_idx -= kBufferSize;
    }
    return buf_.data[rd_idx];
  }

  // Utility function for collecting a 16-bit word from the stream signature,
  // handling wrap around at the end of the circular buffer
  inline uint16_t sig_read16(size_t offset) {
    uint32_t rd_idx = buf_.rd_idx + offset;
    if (rd_idx >= kBufferSize) {
      rd_idx -= kBufferSize;
    }
    uint16_t d = buf_.data[rd_idx++];
    if (rd_idx >= kBufferSize) {
      rd_idx -= kBufferSize;
    }
    return d | (buf_.data[rd_idx++] << 8);
  }

  // Utility function for collecting a 32-bit word from the stream signature,
  // handling wrap around at the end of the circular buffer
  inline uint32_t sig_read32(size_t offset) {
    uint32_t rd_idx = buf_.rd_idx + offset;
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
  /**
   * Stream IDentifier
   */
  unsigned id_;
  /**
   * Have we received the stream signature yet?
   */
  sig_state_t sig_recvd_;
  unsigned sig_cnt_;
  /**
   * Retrieve IN data for this stream?
   */
  bool retrieve_;
  /**
   * Check the received data against expectations?
   */
  bool check_;
  /**
   * Send OUT data for this stream?
   */
  bool send_;
  /**
   * Verbose reporting?
   */
  bool verbose_;
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
     * Offset beyond highest used byte in the buffer
     */
    uint32_t end_idx;
    /**
     * Circular buffer of data being transferred from input to output port
     */
    uint8_t data[kBufferSize];
  } buf_;
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_STREAM_H_
