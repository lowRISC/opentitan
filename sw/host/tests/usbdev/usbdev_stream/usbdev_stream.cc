// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "usbdev_stream.h"

#include <cassert>
#include <cstdio>
#include <unistd.h>

#include "stream_test.h"
#include "usbdev_utils.h"

// TODO: can we move the signature values and LFSR functionality that is common
// to both the device and host ends of the stream to a single file?

// Stream signature words
#define STREAM_SIGNATURE_HEAD 0x579EA01AU
#define STREAM_SIGNATURE_TAIL 0x160AE975U

// Seed numbers for the LFSR generators in each transfer direction for
// the given stream number
#define USBTST_LFSR_SEED(s) (uint8_t)(0x10U + (s)*7U)
#define USBDPI_LFSR_SEED(s) (uint8_t)(0x9BU - (s)*7U)

// Simple LFSR for 8-bit sequences
#define LFSR_ADVANCE(lfsr) \
  (((lfsr) << 1) ^         \
   ((((lfsr) >> 1) ^ ((lfsr) >> 2) ^ ((lfsr) >> 3) ^ ((lfsr) >> 7)) & 1u))

// Detect a stream signature within the byte stream;
// simple restartable parser that drops all bytes until we find a header
// signature.
//
// The signature permits usbdev_stream_test to pass test parameters to this
// program as well as overcoming the issue of the mapping from device
// endpoints/streams to USB ports not being under our control.
ssize_t USBDevStream::sig_detect(ssize_t nrecv) {
  assert(nrecv > 0);
  do {
    if (sig_recvd_ == kSigStateStart) {
      sig_recvd_ = kSigStateCheckHead;
      sig_cnt_ = 0U;
    }

    unsigned rd_idx = buf_.rd_idx + sig_cnt_;
    if (rd_idx >= kBufferSize) {
      rd_idx -= kBufferSize;
    }
    const uint8_t *sp = &buf_.data[rd_idx];
    const size_t tail_offset = offsetof(usbdev_stream_sig_t, tail_sig);

    // Advance the parser beyond this byte
    // Note: valid signature bytes remain in the buffer until the signature is
    // complete

    bool discard = false;
    switch (sig_recvd_) {
      // Check the bytes of the header signature
      case kSigStateCheckHead: {
        const unsigned sh = sig_cnt_ << 3;
        uint8_t match = (uint8_t)(STREAM_SIGNATURE_HEAD >> sh);
        if (match == *sp) {
          if (++sig_cnt_ >= 4U) {
            sig_recvd_ = kSigStateSkipBody;
          }
        } else {
          sig_recvd_ = kSigStateStart;
          discard = true;
        }
      } break;

      // Just collect the signature body for later validation
      case kSigStateSkipBody: {
        if (++sig_cnt_ >= tail_offset) {
          sig_recvd_ = kSigStateCheckTail;
        }
      } break;

      // Check the bytes of the tail signature
      case kSigStateCheckTail: {
        const unsigned sh = (sig_cnt_ - tail_offset) << 3;
        uint8_t match = (uint8_t)(STREAM_SIGNATURE_TAIL >> sh);
        if (match == *sp) {
          if (++sig_cnt_ >= sizeof(usbdev_stream_sig_t)) {
            uint32_t num_bytes;
            uint8_t init_lfsr;
            uint8_t stream;
            uint8_t res1;
            uint8_t res2;

            // We have a complete stream signature; validate it
            stream = sig_read8(offsetof(usbdev_stream_sig_t, stream));
            init_lfsr = sig_read8(offsetof(usbdev_stream_sig_t, init_lfsr));
            res1 = sig_read8(offsetof(usbdev_stream_sig_t, reserved1));
            res2 = sig_read8(offsetof(usbdev_stream_sig_t, reserved2));
            num_bytes = sig_read32(offsetof(usbdev_stream_sig_t, num_bytes));

            if (cfg.verbose) {
              printf("Signature detected: stream #%u LFSR 0x%02x bytes 0x%x\n",
                     stream, init_lfsr, num_bytes);
            }

            // Simple sanity check of the received signature
            if (num_bytes > 0U && num_bytes < 0x10000000U && !res1 && !res2 &&
                stream < STREAMS_MAX) {
              if (cfg.verbose) {
                printf("Signature accepted\n");
              }
              dpi_lfsr_ = USBDPI_LFSR_SEED(stream);
              tst_lfsr_ = init_lfsr;
              transfer_bytes_ = num_bytes;
              sig_recvd_ = kSigStateReceived;
            } else {
              sig_recvd_ = kSigStateStart;
            }
            discard = true;
          }
        } else {
          sig_recvd_ = kSigStateStart;
          discard = true;
        }
      } break;

      default:
        // Note: should not be called once we have a valid stream signature
        assert(!"Invalid/undefined sig_recvd state");
        break;
    }

    if (discard) {
      // Mismatch; discard the checked data, and retry
      if (++rd_idx >= kBufferSize) {
        rd_idx = 0U;
      }
      buf_.rd_idx = rd_idx;
      sig_cnt_ = 0U;
    }

  } while (--nrecv > 0U && sig_recvd_ != kSigStateReceived);

  return nrecv;
}

// Iniitialise a stream between the specified input and output ports
bool USBDevStream::Open(unsigned id, const char *in_name, const char *out_name,
                        uint32_t transfer_bytes) {
  // Remember stream IDentifier
  id_ = id;

  // Not yet received stream signature
  sig_recvd_ = kSigStateStart;

  // Initialise LFSR state
  tst_lfsr_ = USBTST_LFSR_SEED(id);
  dpi_lfsr_ = USBDPI_LFSR_SEED(id);

  // Initialise circular buffer
  buf_.wr_idx = 0U;
  buf_.rd_idx = 0U;

  // Number of bytes to be transferred
  transfer_bytes_ = transfer_bytes;

  // Total counts of bytes received and sent
  bytes_recvd_ = 0U;
  bytes_sent_ = 0U;

  // Open the input and output ports to the board/device for this stream
  in_ = port_open(in_name, false);
  if (in_ < 0) {
    return false;
  }
  out_ = port_open(out_name, true);
  if (out_ < 0) {
    close(in_);
    return false;
  }

  if (cfg.verbose) {
    printf("S%u: input '%s' (%d) output '%s' (%d)\n", id, in_name, in_,
           out_name, out_);
  }

  return true;
}

// Finalise the given stream, releasing all resources
void USBDevStream::Close() {
  // Close any open port handles
  if (in_ >= 0) {
    close(in_);
    in_ = -1;
  }
  if (out_ >= 0) {
    close(out_);
    out_ = -1;
  }
}

// Return an indication of whether this stream has completed its transfer
bool USBDevStream::Completed() const {
  return (!cfg.retrieve || bytes_recvd_ >= transfer_bytes_) &&
         (!cfg.send || bytes_sent_ >= transfer_bytes_);
}

// Service the given data stream
bool USBDevStream::Service() {
  if (cfg.verbose) {
    printf("S%u : rd_idx 0x%x wr_idx 0x%x\n", id_, buf_.rd_idx, buf_.wr_idx);
  }

  // ----- Sending of OUT traffic to device -----

  if (sig_recvd_ == kSigStateReceived) {
    // Decide how much data we should try to write OUT to the device
    uint32_t to_send = kBufferSize - buf_.rd_idx;
    if (buf_.wr_idx >= buf_.rd_idx) {
      to_send = buf_.wr_idx - buf_.rd_idx;
    }
    if (to_send > 0U) {
      ssize_t nsent;
      if (cfg.send) {
        if (cfg.verbose) {
          printf("S%u: Trying to send %u byte(s)\n", id_, to_send);
        }
        // Propagate the modified bytes to the output port
        nsent = send_bytes(out_, &buf_.data[buf_.rd_idx], to_send);
        if (nsent < 0) {
          return false;
        }
      } else {
        nsent = to_send;
      }

      if (cfg.verbose) {
        printf("S%u: %s %zd byte(s)\n", id_, cfg.send ? "Sent" : "Dropped",
               nsent);
      }

      // Update the buffer reading state
      bytes_sent_ += nsent;
      buf_.rd_idx += nsent;
      if (buf_.rd_idx >= kBufferSize) {
        buf_.rd_idx = 0U;
      }
    }
  }

  // ----- Retrieving of IN traffic from device -----

  // Decide how many bytes to try to read into our buffer; do not go beyond
  //   the end of the physical buffer or beyond the current read pointer
  uint32_t to_fetch = kBufferSize - buf_.wr_idx;
  if (buf_.rd_idx > buf_.wr_idx) {
    to_fetch = (buf_.rd_idx - 1) - buf_.wr_idx;
  } else if (to_fetch >= kBufferSize) {
    to_fetch = kBufferSize - 1U;
  }
  if (to_fetch > transfer_bytes_ - bytes_recvd_) {
    to_fetch = transfer_bytes_ - bytes_recvd_;
  }

  uint8_t *dp = &buf_.data[buf_.wr_idx];
  ssize_t nrecvd;
  if (cfg.retrieve) {
    if (cfg.verbose) {
      printf("S%u: Trying to fetch %u byte(s)\n", id_, to_fetch);
    }
    // Read as many bytes as we can from the input port
    nrecvd = recv_bytes(in_, dp, to_fetch);
    if (nrecvd < 0) {
      return false;
    }
  } else {
    if (sig_recvd_ != kSigStateReceived) {
      // Pretend that we've received the expected signature
      // Note: transfer_bytes remains at the requested value
      tst_lfsr_ = USBTST_LFSR_SEED(id_);
      sig_recvd_ = kSigStateReceived;
    }

    // Generate a stream of bytes _as if_ we'd received them correctly from
    // the device
    uint8_t next_lfsr = tst_lfsr_;
    for (unsigned idx = 0U; idx < to_fetch; idx++) {
      dp[idx] = next_lfsr;
      next_lfsr = LFSR_ADVANCE(next_lfsr);
    }
    nrecvd = to_fetch;
  }

  if (nrecvd > 0) {
    // Update the buffer writing state
    buf_.wr_idx += (uint32_t)nrecvd;
    if (buf_.wr_idx >= kBufferSize) {
      buf_.wr_idx = 0U;
    }

    // If we don't yet have a stream signature then we consume all bytes until
    // we have a complete signature
    if (sig_recvd_ != kSigStateReceived) {
      nrecvd = sig_detect(nrecvd);
      // Skip over any signature that we've just consumed
      dp = &buf_.data[buf_.rd_idx];
    }

    if (nrecvd > 0) {
      // Record the time of the first data reception
      if (!received) {
        start_time = time_us();
        received = true;
      }

      if (cfg.verbose) {
        printf("S%u: %s %zd byte(s)\n", id_,
               cfg.retrieve ? "Received" : "Generated", nrecvd);
      }

      // We can just check and overwrite the input data in-situ
      const uint8_t *sp = dp;
      for (unsigned idx = 0U; idx < (unsigned)nrecvd; idx++) {
        uint8_t expected = tst_lfsr_;
        uint8_t recvd = sp[idx];

        // Check whether the received byte is as expected
        if (cfg.check) {
          if (cfg.retrieve && recvd != expected) {
            printf("S%u: Mismatched data from device 0x%02x, expected 0x%02x\n",
                   id_, recvd, expected);
          }
        }

        // Simply XOR the two LFSR-generated streams together
        dp[idx] = recvd ^ dpi_lfsr_;
        if (cfg.verbose) {
          printf("S%u: 0x%02x <- 0x%02x ^ 0x%02x\n", id_, dp[idx], recvd,
                 dpi_lfsr_);
        }

        // Advance our LFSRs
        tst_lfsr_ = LFSR_ADVANCE(tst_lfsr_);
        dpi_lfsr_ = LFSR_ADVANCE(dpi_lfsr_);
      }

      // Update the buffer writing state
      bytes_recvd_ += (uint32_t)nrecvd;
    }
  }

  return true;
}
