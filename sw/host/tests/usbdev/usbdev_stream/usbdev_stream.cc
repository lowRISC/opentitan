// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "usbdev_stream.h"

#include <cassert>
#include <cstdio>
#include <cstring>
#include <iostream>

#include "stream_test.h"
#include "usb_device.h"
#include "usbdev_utils.h"

// Stream signature words.
#define STREAM_SIGNATURE_HEAD 0x579EA01AU
#define STREAM_SIGNATURE_TAIL 0x160AE975U

// Seed numbers for the LFSR generators in each transfer direction for
// the given stream number.
#define USBTST_LFSR_SEED(s) (uint8_t)(0x10U + (s)*7U)
#define USBDPI_LFSR_SEED(s) (uint8_t)(0x9BU - (s)*7U)

// Simple LFSR for 8-bit sequences.
#define LFSR_ADVANCE(lfsr) \
  (((lfsr) << 1) ^         \
   ((((lfsr) >> 1) ^ ((lfsr) >> 2) ^ ((lfsr) >> 3) ^ ((lfsr) >> 7)) & 1u))

USBDevStream::USBDevStream(unsigned id, uint32_t transfer_bytes, bool retrieve,
                           bool check, bool send, bool verbose) {
  // Remember Stream IDentifier and flags.
  SetProperties(id, retrieve, check, send);
  verbose_ = verbose;

  // Stream is not in the process of being closed.
  closing_ = false;

  // Not yet received stream signature.
  sig_recvd_ = kSigStateStart;

  // Initialise LFSR state.
  tst_lfsr_ = USBTST_LFSR_SEED(id);
  dpi_lfsr_ = USBDPI_LFSR_SEED(id);

  // Initialize circular buffer.
  buf_.wr_idx = 0U;
  buf_.rd_idx = 0U;
  buf_.end_idx = 0U;

  // Number of bytes to be transferred.
  transfer_bytes_ = transfer_bytes;

  // Total counts of bytes received and sent.
  bytes_recvd_ = 0U;
  bytes_sent_ = 0U;
}

// Detect a stream signature within the byte stream;
// simple restartable parser that drops all bytes until we find a header
// signature.
//
// The signature permits usbdev_stream_test to pass test parameters to this
// program as well as overcoming the issue of the mapping from device
// endpoints/streams to USB ports not being under our control.
uint32_t USBDevStream::SigDetect(usbdev_stream_sig_t *sig, const uint8_t *sp,
                                 uint32_t nrecv) {
  uint32_t dropped = 0U;
  assert(nrecv > 0);
  do {
    if (sig_recvd_ == kSigStateStart) {
      sig_recvd_ = kSigStateCheckHead;
      sig_cnt_ = 0U;
    }

    // Collect the signature into a structure with appropriate alignment
    // for direct access to members.
    uint8_t *sigp = reinterpret_cast<uint8_t *>(sig);
    sigp[sig_cnt_] = *sp;

    // Advance the parser beyond this byte
    // Note: valid signature bytes remain excluded from the returned count of
    // dropped bytes.
    const size_t tail_offset = offsetof(usbdev_stream_sig_t, tail_sig);
    bool discard = false;
    switch (sig_recvd_) {
      // Check the bytes of the header signature.
      case kSigStateCheckHead: {
        const unsigned sh = sig_cnt_ << 3;
        uint8_t match = (uint8_t)(STREAM_SIGNATURE_HEAD >> sh);
        if (match == *sp) {
          if (++sig_cnt_ >= 4U) {
            sig_recvd_ = kSigStateSkipBody;
          }
        } else {
          discard = true;
        }
      } break;

      // Just collect the signature body for later validation.
      case kSigStateSkipBody: {
        if (++sig_cnt_ >= tail_offset) {
          sig_recvd_ = kSigStateCheckTail;
        }
      } break;

      // Check the bytes of the tail signature
      case kSigStateCheckTail: {
        const unsigned sh = (sig_cnt_ - tail_offset) << 3;
        const uint8_t match = (uint8_t)(STREAM_SIGNATURE_TAIL >> sh);
        if (match == *sp) {
          if (sig_cnt_ >= sizeof(usbdev_stream_sig_t) - 1U) {
            // Note: at this point we could use the signature words to identify
            // the Endianness of the sender and thus reverse the other fields
            // if necessary.

            // Basic sanity check of signature values before we accept it;
            // some of the checking must be stream-type dependent, so this is
            // not a complete guarantee of validity.
            uint8_t stream = sig->stream & USBDevice::kUsbdevStreamFlagID;
            if (sig->num_bytes > 0U && sig->num_bytes < 0x10000000U &&
                stream < STREAMS_MAX) {
              if (verbose_) {
                std::cout << PrefixID() << "Signature accepted" << std::endl;
              }
              sig_recvd_ = kSigStateReceived;
            } else {
              std::cout << PrefixID() << "Signature rejected" << std::endl;
              // Report the signature to explain why it's been rejected.
              SigReport(*sig);
              discard = true;
            }
          } else {
            sig_cnt_++;
          }
        } else {
          discard = true;
        }
      } break;

      default:
        // Note: should not be called once we have a valid stream signature.
        assert(!"Invalid/undefined sig_recvd state");
        break;
    }

    if (discard) {
      // Mismatch; discard the checked data, and resume from the beginning.
      dropped += sig_cnt_ + 1U;
      sig_recvd_ = kSigStateStart;
      sig_cnt_ = 0U;
    }
    // Advance to next byte.
    sp++;
  } while (--nrecv > 0U && sig_recvd_ != kSigStateReceived);

  return dropped;
}

void USBDevStream::SigProcess(const usbdev_stream_sig_t &sig) {
  // Stream IDentifier and flags.
  uint8_t stream = sig.stream & USBDevice::kUsbdevStreamFlagID;
  bool retrieve = ((sig.stream & USBDevice::kUsbdevStreamFlagRetrieve) != 0U);
  bool check = ((sig.stream & USBDevice::kUsbdevStreamFlagCheck) != 0U);
  bool send = ((sig.stream & USBDevice::kUsbdevStreamFlagSend) != 0U);
  SetProperties(stream, retrieve, check, send);

  // If this is the start of the sequence then we also have the number of bytes
  // to be transferred.
  if (!(sig.seq_hi | sig.seq_lo)) {
    transfer_bytes_ = sig.num_bytes;
  }
}

void USBDevStream::SigReport(const usbdev_stream_sig_t &sig) {
  // Sequence number; important for unreliable packet-based streams
  // (Isochronous streams).
  uint16_t seq = sig_read8(offsetof(usbdev_stream_sig_t, seq_lo)) |
                 (sig_read8(offsetof(usbdev_stream_sig_t, seq_hi)) << 8);

  // Stream IDentifier and flags.
  uint8_t stream = sig.stream & USBDevice::kUsbdevStreamFlagID;
  bool retrieve = ((sig.stream & USBDevice::kUsbdevStreamFlagRetrieve) != 0U);
  bool check = ((sig.stream & USBDevice::kUsbdevStreamFlagCheck) != 0U);
  bool send = ((sig.stream & USBDevice::kUsbdevStreamFlagSend) != 0U);

  printf("Signature detected: stream #%u LFSR 0x%02x bytes 0x%x\n", stream,
         sig.init_lfsr, sig.num_bytes);
  printf(" - retrieve %c check %c send %c\n", retrieve ? 'Y' : 'N',
         check ? 'Y' : 'N', send ? 'Y' : 'N');
  printf(" - seq #%u\n", seq);
}

// Return an indication of whether this stream has completed its transfer.
bool USBDevStream::Completed() const {
  return (bytes_recvd_ >= transfer_bytes_) && (bytes_sent_ >= transfer_bytes_);
}

bool USBDevStream::ProvisionSpace(uint8_t **space, uint32_t len) {
  uint32_t space_bytes = SpaceAvailable(space);
  if (space_bytes >= len) {
    return true;
  }

  // If we're failing to allocate sufficient space right at the end of the
  // buffer, wrap sooner.
  if (buf_.rd_idx <= buf_.wr_idx && (kBufferSize - buf_.wr_idx) < len &&
      buf_.rd_idx > len) {
    buf_.end_idx = buf_.wr_idx;
    buf_.wr_idx = 0U;
    // Return pointer to the start of the free space.
    if (space) {
      *space = buf_.data;
    }
    return true;
  }

  return false;
}

uint32_t USBDevStream::SpaceAvailable(uint8_t **space) {
  uint32_t space_bytes = kBufferSize - buf_.wr_idx;
  uint8_t *start = &buf_.data[buf_.wr_idx];

  if (buf_.rd_idx > buf_.wr_idx) {
    // All space is contiguous.
    space_bytes = (buf_.rd_idx - 1U) - buf_.wr_idx;
  } else if (!buf_.rd_idx) {
    // Leave one unused byte at the end of the circular buffer.
    space_bytes--;
  }

  // Return pointer to the start of the free space.
  if (space) {
    *space = start;
  }
  return space_bytes;
}

bool USBDevStream::AddData(const uint8_t *data, uint32_t len) {
  // Ascertain the amount of space available.
  uint32_t space_bytes = SpaceAvailable(nullptr);
  if (space_bytes < len) {
    return false;
  }

  // Size of first contiguous chunk.
  uint32_t chunk = kBufferSize - buf_.wr_idx;
  if (len < chunk) {
    chunk = len;
  }
  if (data) {
    // Data is not already present in the buffer.
    memcpy(&buf_.data[buf_.wr_idx], data, chunk);
    data += chunk;
  }
  buf_.wr_idx += chunk;
  if (buf_.wr_idx > buf_.end_idx) {
    buf_.end_idx = buf_.wr_idx;
  }

  // Write index wraparound.
  if (buf_.wr_idx >= kBufferSize) {
    buf_.wr_idx = 0U;
  }

  return true;
}

void USBDevStream::GenerateData(uint8_t *dp, uint32_t len) {
  // Generate a stream of bytes _as if_ we'd received them correctly from
  // the device
  uint8_t next_lfsr = tst_lfsr_;
  for (unsigned idx = 0U; idx < len; idx++) {
    dp[idx] = next_lfsr;
    next_lfsr = LFSR_ADVANCE(next_lfsr);
  }
}

bool USBDevStream::ProcessData(uint8_t *dp, uint32_t len) {
  bool ok = true;

  if (len > 0U) {
    // Record the time of the first data reception.
    if (!received) {
      start_time = time_us();
      received = true;
    }

    if (verbose_) {
      std::cout << "S" << ID()
                << (cfg.retrieve ? ": Received " : ": Generated ") << len
                << " byte(s)" << std::endl;
    }

    // We can just check and overwrite the input data in-situ.
    const uint8_t *sp = dp;
    for (uint32_t idx = 0U; idx < len; idx++) {
      uint8_t expected = tst_lfsr_;
      uint8_t recvd = sp[idx];

      // Check whether the received byte is as expected.
      if (retrieve_ && check_) {
        if (recvd != expected) {
          printf("S%u: Mismatched data from device 0x%02x, expected 0x%02x\n",
                 id_, recvd, expected);
          ok = false;
        }
      }

      // Simply XOR the two LFSR-generated streams together.
      dp[idx] = recvd ^ dpi_lfsr_;
      if (verbose_) {
        printf("S%u: 0x%02x <- 0x%02x ^ 0x%02x\n", id_, dp[idx], recvd,
               dpi_lfsr_);
      }

      // Advance our LFSRs.
      tst_lfsr_ = LFSR_ADVANCE(tst_lfsr_);
      dpi_lfsr_ = LFSR_ADVANCE(dpi_lfsr_);
    }

    // Update the buffer writing state.
    bytes_recvd_ += len;
  }

  return ok;
}

uint32_t USBDevStream::DataAvailable(uint8_t **data) {
  // Read index wraparound.
  if (buf_.rd_idx >= buf_.end_idx && buf_.wr_idx > 0U &&
      buf_.wr_idx < buf_.rd_idx) {
    buf_.rd_idx = 0U;
  }

  uint32_t data_bytes = buf_.end_idx - buf_.rd_idx;
  uint8_t *start = &buf_.data[buf_.rd_idx];

  if (buf_.wr_idx >= buf_.rd_idx) {
    data_bytes = buf_.wr_idx - buf_.rd_idx;
  }
  if (data) {
    *data = start;
  }
  return data_bytes;
}

bool USBDevStream::DiscardData(uint32_t len) {
  // Ascertain the amount of data available.
  uint32_t data_bytes = DataAvailable(nullptr);
  if (data_bytes < len) {
    return false;
  }

  // Adjust buffer state to discard the specified number of bytes.
  uint32_t chunk = buf_.end_idx - buf_.rd_idx;
  assert(len <= chunk);
  if (len < chunk || (len == chunk && buf_.wr_idx >= buf_.end_idx)) {
    buf_.rd_idx += len;
  } else {
    buf_.rd_idx = len - chunk;
  }

  return true;
}

bool USBDevStream::ConsumeData(uint32_t len) {
  if (!DiscardData(len)) {
    return false;
  }
  // Update the count of transmitted bytes.
  bytes_sent_ += len;
  return true;
}

void USBDevStream::ClearBuffer() {
  // Check that the write index is valid before we advance the read index to
  // clear the buffer.
  assert(buf_.wr_idx < kBufferSize);
  assert(buf_.wr_idx <= buf_.end_idx);
  buf_.rd_idx = buf_.wr_idx;
}

// Service the given data stream; this base class implementation just provides
// some generic progress reporting.
bool USBDevStream::Service() {
  if (verbose_) {
    printf("S%u : rd_idx 0x%x wr_idx 0x%x\n", id_, buf_.rd_idx, buf_.wr_idx);
  }
  return true;
}
