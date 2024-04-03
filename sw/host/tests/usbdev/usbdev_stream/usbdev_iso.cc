// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "usbdev_iso.h"

#include <cassert>
#include <cstdio>

#include "usbdev_utils.h"

// Stub callback function supplied to libusb.
void LIBUSB_CALL USBDevIso::CbStubIN(struct libusb_transfer *xfr) {
  USBDevIso *self = reinterpret_cast<USBDevIso *>(xfr->user_data);
  self->CallbackIN(xfr);
}

void LIBUSB_CALL USBDevIso::CbStubOUT(struct libusb_transfer *xfr) {
  USBDevIso *self = reinterpret_cast<USBDevIso *>(xfr->user_data);
  self->CallbackOUT(xfr);
}

bool USBDevIso::Open(unsigned interface) {
  int rc = dev_->ClaimInterface(interface);
  if (rc < 0) {
    return dev_->ErrorUSB("ERROR: Claiming interface", rc);
  }

  // Retain the interface number.
  interface_ = interface;

  // Remember the (assumed) endpoints which we're using.
  epOut_ = interface + 1U;
  epIn_ = 0x80U | epOut_;

  // No transfers in progress.
  xfrIn_ = nullptr;
  xfrOut_ = nullptr;

  // Expected sequence number of first packet.
  tst_seq_ = 0U;

  // Maximum size of a packet in bytes.
  maxPacketSize_ = USBDevice::kDevIsoMaxPacketSize;

  return true;
}

void USBDevIso::Stop() {
  SetClosing(true);

  int rc = dev_->ReleaseInterface(interface_);
  if (rc < 0) {
    std::cerr << "" << std::endl;
  }
}

void USBDevIso::Pause() {
  SetClosing(true);

  while (inActive_ || outActive_) {
    dev_->Service();
  }

  int rc = dev_->ReleaseInterface(interface_);
  if (rc < 0) {
    std::cerr << "" << std::endl;
  }
}

bool USBDevIso::Resume() {
  SetClosing(false);

  int rc = dev_->ClaimInterface(interface_);
  if (rc < 0) {
    return dev_->ErrorUSB("ERROR: Claiming interface", rc);
  }
  return true;
}

// Return an indication of whether this stream has completed its transfer.
bool USBDevIso::Completed() const {
  // Note: an Isochronous stream presently cannot know whether it has
  // transferred sufficient data for the device-side software to have completed.
  //
  // TODO: perhaps we just time out after a period of inactivity. The device-
  // side software ultimately decides success or failure of the test, at which
  // point the test harness will be terminated.
  return false;
}

// Return a summary report of the stream settings of status.
std::string USBDevIso::Report(bool status, bool verbose) const { return ""; }

void USBDevIso::DumpIsoTransfer(struct libusb_transfer *xfr) const {
  for (int idx = 0U; idx < xfr->num_iso_packets; idx++) {
    struct libusb_iso_packet_descriptor *pack = &xfrIn_->iso_packet_desc[idx];
    std::cout << "Requested " << pack->length << " actual "
              << pack->actual_length << std::endl;
    // Buffer dumping works only because we have just a single Iso packet per
    // transfer.
    buffer_dump(stdout, (uint8_t *)xfr->buffer, pack->actual_length);
  }
}

// Retrieving of IN traffic from device.
bool USBDevIso::ServiceIN() {
  // Ensure that we have enough space available for a full packet; the device
  // software decides upon the length of each packet.
  uint8_t *space;
  bool ok = ProvisionSpace(&space, maxPacketSize_);
  if (ok) {
    if (!xfrIn_) {
      xfrIn_ = dev_->AllocTransfer(kNumIsoPackets);
      if (!xfrIn_) {
        return false;
      }
    }

    dev_->FillIsoTransfer(xfrIn_, epIn_, space, maxPacketSize_, kNumIsoPackets,
                          CbStubIN, this, kIsoTimeout);
    dev_->SetIsoPacketLengths(xfrIn_, maxPacketSize_);

    int rc = dev_->SubmitTransfer(xfrIn_);
    if (rc < 0) {
      return dev_->ErrorUSB("ERROR: Submitting IN transfer", rc);
    }
    inActive_ = true;
  } else {
    inActive_ = false;
  }
  return true;
}

// Sending of OUT traffic to device.
bool USBDevIso::ServiceOUT() {
  // Do we have one or more packets ready for sending?
  if (pktLen_.empty()) {
    // Nothing to propagate at this time.
    outActive_ = false;
  } else {
    uint32_t len = pktLen_.front();
    pktLen_.pop();
    // We should have propagated only valid packets to the OUT side ready for
    // transmission.
    assert(len >= sizeof(usbdev_stream_sig_t));

    uint8_t *data;
    size_t num_bytes = DataAvailable(&data);
    assert(num_bytes >= len);

    // Supply details of the single OUT packet.
    if (!xfrOut_) {
      xfrOut_ = dev_->AllocTransfer(kNumIsoPackets);
      if (!xfrOut_) {
        // Stream is not operational.
        return false;
      }
    }
    dev_->FillIsoTransfer(xfrOut_, epOut_, data, len, kNumIsoPackets, CbStubOUT,
                          this, kIsoTimeout);
    dev_->SetIsoPacketLengths(xfrOut_, len);

    int rc = dev_->SubmitTransfer(xfrOut_);
    if (rc < 0) {
      return dev_->ErrorUSB("ERROR: Submitting OUT transfer", rc);
    }
    outActive_ = true;
  }
  // Stream remains operational, even if it presently has no work on the OUT
  // side.
  return true;
}

bool USBDevIso::Service() {
  if (failed_) {
    return false;
  }
  // (Re)start Isochronous IN traffic if not already in progress.
  if (!inActive_ && !ServiceIN()) {
    return false;
  }
  // (Re)start Isochronous OUT traffic if not already in progress and there is
  // data available to be transmitted.
  if (!outActive_ && !ServiceOUT()) {
    return false;
  }
  return true;
}

// Callback function supplied to libusb for IN transfers.
void USBDevIso::CallbackIN(struct libusb_transfer *xfr) {
  if (xfr->status != LIBUSB_TRANSFER_COMPLETED) {
    std::cerr << PrefixID() << " Invalid/unexpected IN transfer status "
              << xfr->status << std::endl;
    failed_ = true;
    return;
  }

  if (verbose_) {
    std::cout << PrefixID() << "CallbackIN xfr " << xfr << " num_iso_packets "
              << xfr->num_iso_packets << std::endl;
    DumpIsoTransfer(xfr);
  }

  for (int idx = 0U; idx < xfr->num_iso_packets; idx++) {
    struct libusb_iso_packet_descriptor *pack = &xfr->iso_packet_desc[idx];
    if (pack->status != LIBUSB_TRANSFER_COMPLETED) {
      std::cerr << "ERROR: pack " << idx << " status " << pack->status
                << std::endl;
      inActive_ = false;
      return;
    }

    if (pack->actual_length) {
      // Reset signature detection, because a new signature is included at the
      // start of each Isochronous packet.
      SigReset();

      // Check that this packet is recognized as commencing with a valid
      // signature, process the data within the packet, and then retain its
      // details.
      usbdev_stream_sig_t sig;
      uint32_t dropped = SigDetect(&sig, xfr->buffer, pack->actual_length);
      if (SigReceived() && dropped < pack->actual_length &&
          sizeof(usbdev_stream_sig_t) <= pack->actual_length - dropped) {
        // Pick up information from this packet signature.
        SigProcess(sig);

        // Valid packet received; payload includes the signature which we
        // retain and propagate to the caller to permit synchronization.
        uint32_t payload = pack->actual_length - dropped;
        pktLen_.push(payload);

        // Since packets may have been dropped we must use the supplied values
        // of the device-side LFSR
        uint16_t seq = (uint16_t)((sig.seq_hi << 8) | sig.seq_lo);
        if (seq == tst_seq_) {
          if (sig.init_lfsr != tst_lfsr_) {
            std::cerr << "ERROR: Unexpected device-side LFSR value (expected 0x"
                      << std::hex << tst_lfsr_ << " received 0x"
                      << sig.init_lfsr << ")" << std::dec << std::endl;
            inActive_ = false;
            return;
          }
        } else if (seq < tst_seq_) {
          std::cerr << "ERROR: Iso stream packets out of order (expected seq 0x"
                    << std::hex << tst_seq_ << " received 0x" << seq << ")"
                    << std::dec << std::endl;
          inActive_ = false;
          return;
        } else {
          // One or more packets has disappeared; use the supplied LFSR to
          // resynchronize.
          tst_lfsr_ = sig.init_lfsr;
        }

        // Remember the sequence number that we expect to see next.
        tst_seq_ = seq + 1U;

        // Supply the host-side LFSR value so that the device may check the
        // content of received OUT packets.
        const size_t sig_size = sizeof(usbdev_stream_sig_t);
        uint8_t *dp = &xfr->buffer[dropped];
        dp[offsetof(usbdev_stream_sig_t, init_lfsr)] = dpi_lfsr_;
        ProcessData(dp + sig_size, payload - sig_size);

        CommitData(payload);
      } else {
        std::cerr << PrefixID() << " received invalid Iso packet of "
                  << pack->actual_length << " bytes" << std::endl;
      }
    }
  }

  if (CanSchedule()) {
    // Attempt to set up another IN transfer.
    failed_ = !ServiceIN();
  } else {
    inActive_ = false;
  }
}

// Callback function supplied to libusb for OUT transfers.
void USBDevIso::CallbackOUT(struct libusb_transfer *xfr) {
  if (xfr->status != LIBUSB_TRANSFER_COMPLETED) {
    std::cerr << PrefixID() << " Invalid/unexpected OUT transfer status "
              << xfr->status << std::endl;
    failed_ = true;
    return;
  }

  if (verbose_) {
    const void *buf = reinterpret_cast<void *>(xfr->buffer);
    std::cout << PrefixID() << "CallbackOUT xfr " << xfr << " buffer " << buf
              << " num_iso_packets " << xfr->num_iso_packets << std::endl;
    DumpIsoTransfer(xfr);
  }

  for (int idx = 0U; idx < xfr->num_iso_packets; idx++) {
    struct libusb_iso_packet_descriptor *pack = &xfr->iso_packet_desc[idx];
    if (pack->status != LIBUSB_TRANSFER_COMPLETED) {
      std::cout << "ERROR: pack " << idx << " status " << pack->status
                << std::endl;
      outActive_ = false;
      exit(0);
      return;
    }

    if (pack->actual_length) {
      ConsumeData(pack->actual_length);
    }
  }

  if (CanSchedule()) {
    // Attempt to set up another OUT transfer.
    failed_ = !ServiceOUT();
  } else {
    outActive_ = false;
  }
}
