// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdint.h>
#include <string.h>

#include "usb_utils.h"
#include "usbdpi.h"

// Seed numbers for the LFSR generators in each transfer direction for
// the given stream number
#define USBTST_LFSR_SEED(s) (uint8_t)(0x10U + (s)*7U)
#define USBDPI_LFSR_SEED(s) (uint8_t)(0x9BU - (s)*7U)
// Seed number of packet retrying
#define RETRY_LFSR_SEED(s) (uint8_t)(0x24U + (s)*7U)

// Simple LFSR for 8-bit sequences
#define LFSR_ADVANCE(lfsr)     \
  (uint8_t)(                   \
      (uint8_t)((lfsr) << 1) ^ \
      ((((lfsr) >> 1) ^ ((lfsr) >> 2) ^ ((lfsr) >> 3) ^ ((lfsr) >> 7)) & 1U))

// Stream signature words
#define STREAM_SIGNATURE_HEAD 0x579EA01AU
#define STREAM_SIGNATURE_TAIL 0x160AE975U

// Size of stream signature
#define SIZEOF_STREAM_SIGNATURE 0x10U

// Verbose logging/diagnostic reporting
// TODO: consider folding this into the existing log level
static const bool verbose = false;

// Single letter prefix indicating the transfer type
static const char xfr_sym[] = {'C', 'X', 'B', 'I'};

// Determine the next stream for which IN data packets shall be requested
static inline unsigned in_stream_next(usbdpi_ctx_t *ctx);

// Determine the next stream for which OUT data shall be sent
static inline unsigned out_stream_next(usbdpi_ctx_t *ctx);

// Check a data packet received from the test software (usbdev_stream_test)
static bool stream_data_check(usbdpi_ctx_t *ctx, usbdpi_stream_t *s,
                              const usbdpi_transfer_t *rx, unsigned offset,
                              bool accept);

// Generate a data packet as if it had been received from the device
static usbdpi_transfer_t *stream_data_gen(usbdpi_ctx_t *ctx, usbdpi_stream_t *s,
                                          unsigned len);

// Check a data packet received from the test software (usbdev_stream_test)
// and collect the data, combined with our LFSR-generated random stream,
// for later transmission back to the device
static usbdpi_transfer_t *stream_data_process(usbdpi_ctx_t *ctx,
                                              usbdpi_stream_t *s,
                                              usbdpi_transfer_t *rx);

// Check the stream signature
static bool stream_sig_check(usbdpi_ctx_t *ctx, usbdpi_stream_t *s,
                             usbdpi_transfer_t *rx);

// Determine the next stream for which IN data packets shall be requested
inline unsigned in_stream_next(usbdpi_ctx_t *ctx) {
  uint8_t id = ctx->stream_in;
  if (++id >= ctx->nstreams) {
    id = 0U;
  }
  ctx->stream_in = id;
  return id;
}

// Determine the next stream for which OUT data shall be sent
inline unsigned out_stream_next(usbdpi_ctx_t *ctx) {
  uint8_t id = ctx->stream_out;
  if (++id >= ctx->nstreams) {
    id = 0U;
  }
  ctx->stream_out = id;
  return id;
}

// Initialize streaming state for the given number of streams
bool streams_init(usbdpi_ctx_t *ctx, unsigned nstreams,
                  const uint8_t xfr_types[], bool retrieve, bool checking,
                  bool retrying, bool send) {
  assert(ctx);

  // Can we support the requested number of streams?
  if (!nstreams || nstreams > USBDPI_MAX_STREAMS) {
    return false;
  }

  if (verbose) {
    printf("[usbdpi] Stream test running with %u streams(s)\n", nstreams);
    printf("[usbdpi] - retrieve %c checking %c retrying %c send %c\n",
           retrieve ? 'Y' : 'N', checking ? 'Y' : 'N', retrying ? 'Y' : 'N',
           send ? 'Y' : 'N');
  }

  // Remember the number of streams and initialize the arbitration of
  // IN and OUT traffic
  ctx->nstreams = nstreams;
  ctx->stream_in = 0U;
  ctx->stream_out = nstreams - 1U;

  for (unsigned id = 0U; id < nstreams; id++) {
    // Remember the Stream IDentifier
    ctx->stream[id].id = id;
    // Poll device for IN packets in streaming test?
    ctx->stream[id].retrieve = retrieve;
    // Attempt to sent OUT packets to device in streaming test?
    ctx->stream[id].send = send;
    // Checking of received data against expected LFSR output
    ctx->stream[id].checking = checking;
    // We are expecting a stream signature in the first packet
    ctx->stream[id].sig_expected = true;
    // Request retrying of IN packets, feigning error
    ctx->stream[id].retrying = retrying;
    // Transfer type
    ctx->stream[id].xfr_type = xfr_types[id];
    // Endpoints to be used by this stream
    ctx->stream[id].ep_in = 1U + id;
    ctx->stream[id].ep_out = 1U + id;
    // Expected sequence number of first packet
    ctx->stream[id].tst_seq = 0U;
    // LFSR state for this byte stream
    ctx->stream[id].tst_lfsr = USBTST_LFSR_SEED(id);
    ctx->stream[id].dpi_lfsr = USBDPI_LFSR_SEED(id);
    ctx->stream[id].dpi_rewind_lfsr = ctx->stream[id].dpi_lfsr;
    // LFSR-controlled packet retrying state
    ctx->stream[id].retry_lfsr = RETRY_LFSR_SEED(id);
    ctx->stream[id].nretries = 0U;
    // No received packets
    ctx->stream[id].received = NULL;
  }
  return true;
}

// Check a data packet received from the test software (usbdev_stream_test)
bool stream_data_check(usbdpi_ctx_t *ctx, usbdpi_stream_t *s,
                       const usbdpi_transfer_t *rx, unsigned offset,
                       bool accept) {
  assert(rx);

  // The byte count _includes_ the DATAx PID and the two CRC bytes
  //
  // Note: we are expecting a LFSR-generated byte stream, but we do not
  //       make assumptions about the number or size of the data packets
  //       that make up the stream

  unsigned num_bytes = transfer_length(rx);
  unsigned idx = rx->data_start + 1u;  // Skip past the DATAx PID
  bool ok = false;

  // Validate the received packet - data length valid and checksum present
  if (num_bytes >= sizeof(rx->data) || idx + 1u + offset > num_bytes) {
    printf("[usbdpi] Unexpected/malformed data packet (0x%x 0x%x)\n", idx,
           num_bytes);
  } else {
    // Data field within received packet
    const uint8_t *sp = &rx->data[idx];
    num_bytes -= 3u;

    // Check that the CRC16 checksum of the data field is as expected
    uint16_t rx_crc = sp[num_bytes] | (sp[num_bytes + 1u] << 8);
    uint16_t crc = CRC16(sp, num_bytes);
    if (rx_crc != crc) {
      printf("[usbdpi] Mismatched CRC16 0x%04x received, expected 0x%04x\n",
             rx_crc, crc);
    } else {
      // Data toggle synchronization
      unsigned pid = ctx->ep_in[s->ep_in].next_data;
      if (rx->data[0] == pid) {
        // If we've decided to reject this packet then we still check its
        // content but we do not advance the data toggle because we're
        // pretending that we didn't receive it successfully
        if (accept) {
          ctx->ep_in[s->ep_in].next_data = DATA_TOGGLE_ADVANCE(pid);
        }

        // Tentatively acceptable, but we still have to check and report any and
        // all mismatched bytes
        ok = accept;
      }

      // Iff running a performance investigation, checking may be undesired
      // because it causes us to reject and retry the transmission
      if (s->checking) {
        // Advance to the start of the data to be checked; for Isochronous
        // traffic there will be a signature at the start of every packet
        sp += offset;
        num_bytes -= offset;

        // Note: use a local copy of the LFSR so that we can check the data
        //       field even on those packets that we choose to reject
        uint8_t tst_lfsr = s->tst_lfsr;
        while (num_bytes-- > 0U) {
          uint8_t recvd = *sp++;
          if (recvd != tst_lfsr) {
            printf(
                "[usbdpi] %c%u: Mismatched data from device 0x%02x, "
                "expected 0x%02x\n",
                xfr_sym[s->xfr_type], s->id, recvd, tst_lfsr);
            ok = false;
          }
          // Advance our local LFSR
          tst_lfsr = LFSR_ADVANCE(tst_lfsr);
        }

        // Update the LFSR only if we've accepted valid data and will not
        // be receiving this data again
        if (accept && ok) {
          s->tst_lfsr = tst_lfsr;
        }
      } else {
        printf("[usbdpi] Warning: Stream data checking disabled\n");
      }
    }
  }

  return ok;
}

// Generate a data packet as if it had been received from the device
usbdpi_transfer_t *stream_data_gen(usbdpi_ctx_t *ctx, usbdpi_stream_t *s,
                                   unsigned len) {
  // TODO: this code presesntly does not support Isochronous streams
  usbdpi_transfer_t *tr = transfer_alloc(ctx);
  if (tr) {
    // Pretend that we have successfully received the packet with the correct
    // data toggling...
    uint8_t data = ctx->ep_in[s->ep_in].next_data;
    ctx->ep_in[s->ep_in].next_data = DATA_TOGGLE_ADVANCE(data);
    // ...and that the data is as expected
    uint8_t *dp = transfer_data_start(tr, data, len);
    for (unsigned idx = 0U; idx < len; idx++) {
      dp[idx] = s->tst_lfsr;
      s->tst_lfsr = LFSR_ADVANCE(s->tst_lfsr);
    }
    transfer_data_end(tr, dp + len);
  }
  return tr;
}

// Process a received data packet to produce a corresponding reply packet
// by XORing our LFSR output with the received data
//
// Note: for now we do this even if the received data mismatches because
//       only the CPU software has the capacity to decide upon and report
//       test status
usbdpi_transfer_t *stream_data_process(usbdpi_ctx_t *ctx, usbdpi_stream_t *s,
                                       usbdpi_transfer_t *rx) {
  // Note: checkStreamData has already been called on this packet
  assert(rx);

  // The byte count _includes_ the DATAx PID and the two CRC bytes
  unsigned num_bytes = transfer_length(rx);
  num_bytes -= 3u;

  // Data field within received packet
  const uint8_t *sp = transfer_data_field(rx);
  if (!sp)
    return NULL;

  // Allocate a new buffer for the reply
  usbdpi_transfer_t *reply = transfer_alloc(ctx);
  assert(reply);

  // Construct OUT token packet to the target endpoint, using the
  // appropriate DATAx PID
  const uint8_t ep_out = s->ep_out;
  transfer_token(reply, USB_PID_OUT, ctx->dev_address, ep_out);
  uint8_t *dp =
      transfer_data_start(reply, ctx->ep_out[ep_out].next_data, num_bytes);
  assert(dp);

  // For Isochronous streams each packet commences with a signature that
  // specifies the packet sequence number and the device-side LFSR; we must
  // replace the LFSR value with our own so that the device is able to check
  // the returned packet data.

  if (s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS) {
    // If this is not the case, we should not have accepted the packet.
    assert(num_bytes >= SIZEOF_STREAM_SIGNATURE);

    // Copy the signature bytes across, supplying our starting LFSR value so
    // that the device software may run forwards, past any packets that may have
    // been dropped.
    memcpy(dp, sp, SIZEOF_STREAM_SIGNATURE);
    dp[4] = s->dpi_lfsr;
    dp += SIZEOF_STREAM_SIGNATURE;
    sp += SIZEOF_STREAM_SIGNATURE;

    num_bytes -= SIZEOF_STREAM_SIGNATURE;
  }

  // Keep a record of the LFSR, so that we may rewind in the event of a delivery
  // failure
  s->dpi_rewind_lfsr = s->dpi_lfsr;

  while (num_bytes-- > 0U) {
    uint8_t recvd = *sp++;

    // Simply XOR the two LFSR-generated streams together
    *dp++ = recvd ^ s->dpi_lfsr;
    if (verbose) {
      printf("[usbdpi] 0x%02x <- 0x%02x ^ 0x%02x\n", *(dp - 1), recvd,
             s->dpi_lfsr);
    }
    // Advance our local copy of the LFSR
    s->dpi_lfsr = LFSR_ADVANCE(s->dpi_lfsr);
  }

  transfer_data_end(reply, dp);

  return reply;
}

// Check the stream signature
bool stream_sig_check(usbdpi_ctx_t *ctx, usbdpi_stream_t *s,
                      usbdpi_transfer_t *rx) {
  // Packet should be PID, data field and CRC16 for non-Isochronous,
  // or at least that for Isochronous; Iso streams carry a signature in every
  // packet.
  const size_t min_len = 3U + 0x10U;
  size_t len = transfer_length(rx);
  bool ok = (len == min_len);

  if (s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS) {
    ok = (len >= min_len);
  }
  if (ok) {
    const uint8_t *sig = transfer_data_field(rx);
    if (sig) {
      // Signature format:
      //   Bits Description
      //   32   head signature
      //   8    initial vaue of LFSR
      //   8    stream number
      //   16   sequence number
      //   32   number of bytes to be transferred
      //   32   tail signature
      // Note: all 32-bit quantities are in little endian order

      uint32_t num_bytes = get_le32(&sig[8]);
      if (verbose) {
        printf("[usbdpi] Stream signature at %p head 0x%x tail 0x%x\n", sig,
               get_le32(&sig[0]), get_le32(&sig[12]));
      }

      // Basic validation check; words are transmitted in little endian order
      if (get_le32(&sig[0]) == STREAM_SIGNATURE_HEAD &&
          get_le32(&sig[12]) == STREAM_SIGNATURE_TAIL &&
          // sanity check on transfer length, though we rely upon the CPU
          // software to send, receive and count the number of bytes
          num_bytes > 0U && num_bytes < 0x10000000U) {
        // For Isochronous streams the sequence number identifies the packet
        // (and informs us whether any have been dropped), and crucially it
        // also specifies the intiial value of the device-side LFSR for  _this_
        // packet.
        uint16_t seq = get_le16(&sig[6]);
        if (s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS) {
          if (verbose) {
            printf("[usbdpi] S#%u: seq 0x%04x\n", s->id, seq);
          }
          if (seq < s->tst_seq) {
            printf(
                "[usbdpi] Iso stream packets out of order (expected seq 0x%x"
                " received 0x%x)\n",
                s->tst_seq, seq);
            return false;
          } else if (seq > s->tst_seq) {
            printf("[usbdpi] Iso stream #%u dropped %u packet(s)\n", s->id,
                   seq - s->tst_seq);
          }
          // Next sequence number expected
          s->tst_seq = seq + 1U;
          // Initial device-side LFSR for this packet
          s->tst_lfsr = sig[4];
          // Data toggle synchronization is not used for Iso streams
          ctx->ep_in[s->ep_in].next_data = USB_PID_DATA0;
        } else {
          // This check is only performed on the first packet, since the non-Iso
          // streams have only a single signature
          if (seq != s->tst_seq) {
            printf(
                "[usbdpi] Unexpected stream packet (expected seq 0x%x"
                " received 0x%x)\n",
                s->tst_seq, seq);
            return false;
          }
          // Advance our sequence number
          s->tst_seq++;
          // Signature includes the initial value of the device-side LFSR
          s->tst_lfsr = sig[4];
          // Update data toggle
          uint8_t pid = transfer_data_pid(rx);
          ctx->ep_in[s->ep_in].next_data = DATA_TOGGLE_ADVANCE(pid);
        }
        return true;
      }
    }
  }
  return false;
}

// Service streaming data (usbdev_stream_test)
// TODO: this function should probably be split into multiple functions now...
void streams_service(usbdpi_ctx_t *ctx) {
  if (verbose) {
    //    printf("[usbdpi] streams_service hostSt %u in %u out %u\n",
    //    ctx->hostSt,
    //           ctx->stream_in, ctx->stream_out);
  }

  // Maximum time for transmission of a packet ought to be circa 80 bytes of
  // data, 640 bits. Allowing for bitstuffing this means we need to leave ~800
  const unsigned min_time_left = 800U;

  switch (ctx->hostSt) {
    // --------------------------------------------
    // Try to transmit a data packet to the device
    // --------------------------------------------
    case HS_STARTFRAME:
    case HS_STREAMOUT: {
      // Decide whether we have enough time within this frame to attempt
      // another transmission
      uint32_t next_frame = ctx->frame_start + FRAME_INTERVAL;
      if ((next_frame - ctx->tick_bits) > min_time_left) {
        unsigned id = out_stream_next(ctx);
        usbdpi_stream_t *s = &ctx->stream[id];
        if (verbose) {
          printf("[usbdpi] OUT considering #%u received %p send %u\n", id,
                 s->received, s->send ? 1 : 0);
        }
        // Default to 'nothing to send, try receiving'...
        ctx->hostSt = HS_STREAMIN;

        if (s->send) {
          // Start by trying to transmit a data packet that we've received, if
          // any
          if (s->received) {
            if (ctx->sending) {
              transfer_release(ctx, ctx->sending);
              ctx->sending = NULL;
            }

            // Scramble the oldest received packet with our LFSR-generated byte
            // stream and send it to the device
            usbdpi_transfer_t *reply = stream_data_process(ctx, s, s->received);
            if (reply) {
              ctx->bus_state = kUsbBulkOut;
              switch (s->xfr_type) {
                case USB_TRANSFER_TYPE_INTERRUPT:
                  ctx->bus_state = kUsbInterruptOut;
                  break;
                case USB_TRANSFER_TYPE_BULK:
                  ctx->bus_state = kUsbBulkOut;
                  break;
                default:
                  assert(s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS);
                  ctx->bus_state = kUsbIsoOut;
                  break;
              }
              uint32_t max_bits = transfer_length(reply) * 10 + 160;  // HACK
              transfer_send(ctx, reply);
              ctx->wait = USBDPI_TIMEOUT(ctx, max_bits);
              // Sending...
              ctx->lastrxpid = 0;
              ctx->hostSt = HS_WAITACK;
            }
          }
        } else {
          // We're not sending anything - discard any received data
          while (s->received) {
            usbdpi_transfer_t *tr = s->received;
            s->received = tr->next;
            transfer_release(ctx, tr);
          }
        }
      } else {
        // Wait until the next bus frame
        ctx->hostSt = HS_NEXTFRAME;
      }
    } break;

    // Await acknowledgement of the packet that we just transmitted
    case HS_WAITACK: {
      usbdpi_stream_t *s = &ctx->stream[ctx->stream_out];
      if (ctx->sending) {
        // Forget reference to the buffer we just tried to send; the received
        // packet remains in the list of received buffers to try again later
        transfer_release(ctx, ctx->sending);
        ctx->sending = NULL;
      }

      // Bulk transfer stream?
      bool bulk = false;
      // Was the data packet accepted?
      bool accepted = false;

      switch (s->xfr_type) {
        case USB_TRANSFER_TYPE_BULK:
          bulk = true;
          // no break
        case USB_TRANSFER_TYPE_INTERRUPT:
          if (ctx->bus_state == (bulk ? kUsbBulkOutAck : kUsbInterruptOutAck)) {
            if (verbose) {
              printf("[usbdpi] OUT - response is PID 0x%02x from device (%s)\n",
                     ctx->lastrxpid, decode_pid(ctx->lastrxpid));
            }

            switch (ctx->lastrxpid) {
              case USB_PID_ACK: {
                accepted = true;
              } break;

              // We may receive a NAK from the device if it is unable to receive
              // the packet right now
              case USB_PID_NAK:
                // Rewind the LFSR in preparation for trying again
                s->dpi_lfsr = s->dpi_rewind_lfsr;
                // TODO: we should have counting code here to kill the test if
                // transmission is rejected too many times; at present, however,
                // we will try too rapidly and would give up too soon.
                printf(
                    "[usbdpi] frame 0x%x tick_bits 0x%x NAK received "
                    "from device\n",
                    ctx->frame, ctx->tick_bits);
                ctx->hostSt = HS_STREAMIN;
                break;

              default:
                printf("[usbdpi] Unexpected PID 0x%02x from device (%s)\n",
                       ctx->lastrxpid, decode_pid(ctx->lastrxpid));
                ctx->hostSt = HS_ERROR;
                break;
            }
          } else if (ctx->tick_bits >= ctx->wait) {
            printf("[usbdpi] Timed out waiting for OUT response\n");
            ctx->hostSt = HS_ERROR;
          }
          break;
        default:
          assert(s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS);
          // No response expected for Isochronous
          if (ctx->bus_state == kUsbIsoOut) {
            accepted = true;
          } else {
            printf("[usbdpi] Unexpected device response to Iso OUT %u\n",
                   ctx->bus_state);
            ctx->hostSt = HS_ERROR;
          }
          break;
      }

      if (accepted) {
        // Transmitted packet was accepted, so we can retire it...
        usbdpi_stream_t *s = &ctx->stream[ctx->stream_out];
        usbdpi_transfer_t *rx = s->received;
        assert(rx);
        s->received = rx->next;
        transfer_release(ctx, rx);
        // No data toggling for Isochronous
        if (s->xfr_type != USB_TRANSFER_TYPE_ISOCHRONOUS) {
          uint8_t ep_out = s->ep_out;
          ctx->ep_out[ep_out].next_data =
              DATA_TOGGLE_ADVANCE(ctx->ep_out[ep_out].next_data);
        }
        ctx->hostSt = HS_STREAMIN;
      }
    } break;

    // ---------------------------------------------
    // Try to collect a data packet from the device
    // ---------------------------------------------
    case HS_STREAMIN: {
      // Decide whether we have enough time within this frame to attempt
      // another fetch
      //
      // TODO:  find out what the host behaviour should be at this point;
      //        the device must be required to respond within a certain
      //        time interval, and then the bus transmission speed
      //        determines the maximum delay
      uint32_t next_frame = ctx->frame_start + FRAME_INTERVAL;
      if ((next_frame - ctx->tick_bits) > min_time_left) {
        unsigned id = in_stream_next(ctx);
        usbdpi_stream_t *s = &ctx->stream[id];
        if (verbose) {
          printf("[usbdpi] IN considering #%u retrieve %u\n", id,
                 s->retrieve ? 1 : 0);
        }
        if (s->retrieve) {
          // Ensure that a buffer is available for constructing a transfer
          usbdpi_transfer_t *tr = ctx->sending;
          if (!tr) {
            tr = transfer_alloc(ctx);
            assert(tr);
            ctx->sending = tr;
          }

          transfer_token(tr, USB_PID_IN, ctx->dev_address, s->ep_in);

          transfer_send(ctx, tr);

          switch (s->xfr_type) {
            case USB_TRANSFER_TYPE_INTERRUPT:
              ctx->bus_state = kUsbInterruptInToken;
              break;
            case USB_TRANSFER_TYPE_BULK:
              ctx->bus_state = kUsbBulkInToken;
              break;
            default:
              assert(s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS);
              ctx->bus_state = kUsbIsoInToken;
              break;
          }

          ctx->hostSt = HS_WAIT_PKT;
          ctx->lastrxpid = 0;
        } else {
          // We're not required to poll for IN data, but if we're sending we
          //   must still fake the reception of valid packet data because
          //   the sw test will be expecting valid data
          if (s->send && !s->received) {
            // For simplicity we just create max length packets
            const unsigned len = USBDEV_MAX_PACKET_SIZE;
            s->received = stream_data_gen(ctx, s, len);
          }
          ctx->hostSt = HS_STREAMOUT;
        }
      } else {
        // Wait until the next bus frame
        ctx->hostSt = HS_NEXTFRAME;
      }
    } break;

    case HS_WAIT_PKT:
      // Wait max time for a response + packet
      ctx->wait = ctx->tick_bits + 18 + 8 + 8 + 64 * 8 + 16;
      ctx->hostSt = HS_ACKIFDATA;
      break;

    case HS_ACKIFDATA: {
      unsigned id = ctx->stream_in;
      usbdpi_stream_t *s = &ctx->stream[id];

      // Have we received a reply?
      bool got_reply = false;
      switch (s->xfr_type) {
        case USB_TRANSFER_TYPE_BULK:
          got_reply = ctx->recving && ctx->bus_state == kUsbBulkInData;
          break;
        case USB_TRANSFER_TYPE_INTERRUPT:
          got_reply = ctx->recving && ctx->bus_state == kUsbInterruptInData;
          break;
        case USB_TRANSFER_TYPE_ISOCHRONOUS:
          got_reply = ctx->recving && ctx->bus_state == kUsbIsoInData;
          break;
        default:
          // TODO: we do NOT support control transfers at present!
          assert(s->xfr_type == USB_TRANSFER_TYPE_CONTROL);
          printf("[usbdpi] Control Transfer type not yet supported");
          ctx->hostSt = HS_ERROR;
          break;
      }

      if (got_reply) {
        // We have a response from the device
        switch (ctx->lastrxpid) {
          case USB_PID_DATA0:
          case USB_PID_DATA1: {
            // Steal the received packet; it belongs to the stream
            usbdpi_transfer_t *rx = ctx->recving;
            assert(rx);
            ctx->recving = NULL;

            // Decide whether we want to ACK or NAK this packet
            bool accept;
            if (s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS) {
              // The device will return a zero length packet if there is no
              // pending data for this Isochronous IN endpoint
              // Note: a ZLP still implies a transfer of PID and CRC16 bytes
              accept = (transfer_length(rx) > 3U);
            } else {
              if (s->retrying && s->nretries) {
                accept = false;
                s->nretries--;
              } else {
                // Decide the number of retries for the next data packet
                // Note: by randomizing the number of retries, rather than
                // independently deciding each accept/reject, we guarantee an
                // upper bound on the run time
                switch (s->retry_lfsr & 7U) {
                  case 7U:
                    s->nretries = 3U;
                    break;
                  case 6U:
                  case 5U:
                    s->nretries = 2U;
                    break;
                  case 4U:
                    s->nretries = 1U;
                    break;
                  default:
                    s->nretries = 0U;
                    break;
                }
                s->retry_lfsr = LFSR_ADVANCE(s->retry_lfsr);
                accept = true;
              }

              if (!accept) {
                printf("[usbdpi] Requesting resend of data\n");
                usb_monitor_log(ctx->mon,
                                "[usbdpi] Requesting resend of data\n");
              }
            }

            if (accept) {
              // Offset of LFSR byte stream within packet
              unsigned offset = 0U;

              if (s->sig_expected) {
                accept = stream_sig_check(ctx, s, rx);
                if (accept) {
                  offset = SIZEOF_STREAM_SIGNATURE;
                  if (s->xfr_type != USB_TRANSFER_TYPE_ISOCHRONOUS) {
                    // For non-Isochronous streams, we can rely upon the first
                    // packet being just the signature, identifying the stream.
                    transfer_release(ctx, rx);
                    rx = NULL;
                  }
                } else {
                  printf("[usbdpi] sig check failed\n");
                  // TODO: should probably transition to error state here?
                  accept = false;
                }
              }

              // Check the remaining bytes of the packet, if any
              if (rx && offset < transfer_length(rx)) {
                if (!stream_data_check(ctx, s, rx, offset, accept)) {
                  accept = false;
                }
              }
            }

            // Not yet handled this packet?
            if (rx) {
              if (accept) {
                // Collect the received packets in preparation for later
                // transmission with modification back to the device
                usbdpi_transfer_t *tr = s->received;
                if (tr) {
                  while (tr->next)
                    tr = tr->next;
                  tr->next = rx;
                } else {
                  s->received = rx;
                }
              } else {
                transfer_release(ctx, rx);
              }
            }

            // For non-isochronous transfers, we now ACK/NAK the data, and we
            // expect no further signatures if we've accepted the data.
            if (s->xfr_type != USB_TRANSFER_TYPE_ISOCHRONOUS) {
              usbdpi_transfer_t *tr = ctx->sending;
              assert(tr);

              transfer_status(ctx, tr, accept ? USB_PID_ACK : USB_PID_NAK);

              if (accept) {
                s->sig_expected = false;
              }
            }

            ctx->hostSt = HS_STREAMOUT;
          } break;

          case USB_PID_NAK:
            if (s->xfr_type == USB_TRANSFER_TYPE_ISOCHRONOUS) {
              // Isochronous streams should not be receiving any ACKs/NAKs
              printf("[usbdpi] NAK response from Iso stream");
              ctx->hostSt = HS_ERROR;
            } else {
              // No data available
              ctx->hostSt = HS_STREAMOUT;
            }
            break;

          default:
            printf("[usbdpi] Unexpected PID 0x%02x from device (%s)\n",
                   ctx->lastrxpid, decode_pid(ctx->lastrxpid));
            ctx->hostSt = HS_NEXTFRAME;
            break;
        }
      } else if (ctx->tick_bits >= ctx->wait) {
        printf("[usbdpi] Timed out waiting for IN response\n");
        ctx->hostSt = HS_ERROR;
      }
    } break;

    case HS_ERROR:
      // TODO: report failure (#17259)
      assert(!"Unexpected behavior in streaming test");
      ctx->hostSt = HS_NEXTFRAME;
      break;

    default:
      assert(ctx->hostSt == HS_NEXTFRAME);
      ctx->hostSt = HS_NEXTFRAME;
      break;
  }
}
