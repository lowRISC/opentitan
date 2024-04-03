// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "usbdev_int.h"

#include <cassert>
#include <cstdio>

#include "usbdev_utils.h"

// Stub callback function supplied to libusb.
void LIBUSB_CALL USBDevInt::CbStubIN(struct libusb_transfer *xfr) {
  USBDevInt *self = reinterpret_cast<USBDevInt *>(xfr->user_data);
  self->CallbackIN(xfr);
}

void LIBUSB_CALL USBDevInt::CbStubOUT(struct libusb_transfer *xfr) {
  USBDevInt *self = reinterpret_cast<USBDevInt *>(xfr->user_data);
  self->CallbackOUT(xfr);
}

bool USBDevInt::Open(unsigned interface) {
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

  maxPacketSize_ = USBDevice::kDevDataMaxPacketSize;

  return true;
}

void USBDevInt::Stop() {
  SetClosing(true);

  int rc = dev_->ReleaseInterface(interface_);
  if (rc < 0) {
    std::cerr << "" << std::endl;
  }
}

void USBDevInt::Pause() {
  SetClosing(true);

  if (verbose_) {
    std::cout << PrefixID() << "waiting to close" << std::endl;
  }
  while (inActive_ || outActive_) {
    dev_->Service();
  }
  if (verbose_) {
    std::cout << PrefixID() << " closed" << std::endl;
  }

  int rc = dev_->ReleaseInterface(interface_);
  if (rc < 0) {
    std::cerr << "" << std::endl;
  }
}

bool USBDevInt::Resume() {
  SetClosing(false);

  int rc = dev_->ClaimInterface(interface_);
  if (rc < 0) {
    return dev_->ErrorUSB("ERROR: Claiming interface", rc);
  }
  return true;
}

// Return a summary report of the stream settings of status.
std::string USBDevInt::Report(bool status, bool verbose) const { return ""; }

void USBDevInt::DumpIntTransfer(struct libusb_transfer *xfr) const {
  const void *buf = reinterpret_cast<void *>(xfr->buffer);
  std::cout << "Buffer " << buf << " length " << xfr->length
            << " => actual length " << xfr->actual_length << std::endl;
  buffer_dump(stdout, xfr->buffer, xfr->actual_length);
}

// Retrieving of IN traffic from device.
bool USBDevInt::ServiceIN() {
  // Ensure that we have enough space available for a full packet; the device
  // software decides upon the length of each packet.
  uint8_t *space;
  bool ok = ProvisionSpace(&space, maxPacketSize_);
  if (ok) {
    uint32_t to_fetch = maxPacketSize_;
    if (to_fetch > transfer_bytes_ - bytes_recvd_) {
      to_fetch = transfer_bytes_ - bytes_recvd_;
    }

    if (!xfrIn_) {
      xfrIn_ = dev_->AllocTransfer(0U);
      if (!xfrIn_) {
        return false;
      }
    }

    if (bulk_) {
      dev_->FillBulkTransfer(xfrIn_, epIn_, space, to_fetch, CbStubIN, this,
                             kDataTimeout);
    } else {
      dev_->FillIntTransfer(xfrIn_, epIn_, space, to_fetch, CbStubIN, this,
                            kDataTimeout);
    }

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
bool USBDevInt::ServiceOUT() {
  // Do we have any data ready to send?
  uint8_t *data;
  uint32_t num_bytes = DataAvailable(&data);
  if (num_bytes > 0U) {
    // Supply details of the single OUT packet.
    if (!xfrOut_) {
      xfrOut_ = dev_->AllocTransfer(0U);
      if (!xfrOut_) {
        // Stream is not operational.
        return false;
      }
    }

    if (bulk_) {
      dev_->FillBulkTransfer(xfrOut_, epOut_, data, num_bytes, CbStubOUT, this,
                             kDataTimeout);
    } else {
      dev_->FillIntTransfer(xfrOut_, epOut_, data, num_bytes, CbStubOUT, this,
                            kDataTimeout);
    }

    int rc = dev_->SubmitTransfer(xfrOut_);
    if (rc < 0) {
      return dev_->ErrorUSB("ERROR: Submitting OUT transfer", rc);
    }
    outActive_ = true;
  } else {
    // Nothing to propagate at this time.
    outActive_ = false;
  }
  // Stream remains operational, even if it presently has no work on the OUT
  // side.
  return true;
}

bool USBDevInt::Service() {
  if (failed_) {
    return false;
  }
  // (Re)start IN traffic if not already in progress.
  if (!inActive_ && !ServiceIN()) {
    return false;
  }
  // (Re)start OUT traffic if not already in progress and there is
  // data available to be transmitted.
  if (!outActive_ && !ServiceOUT()) {
    return false;
  }
  return true;
}

// Callback function supplied to libusb for IN transfers.
void USBDevInt::CallbackIN(struct libusb_transfer *xfr) {
  if (xfr->status != LIBUSB_TRANSFER_COMPLETED) {
    std::cerr << PrefixID() << " Invalid/unexpected IN transfer status "
              << xfr->status << std::endl;
    std::cerr << "length " << xfr->length << " actual " << xfr->actual_length
              << std::endl;
    failed_ = true;
    return;
  }

  if (verbose_) {
    std::cout << PrefixID() << "CallbackIN xfr " << xfr << std::endl;
    DumpIntTransfer(xfr);
  }

  // Collect and parse signature bytes at the start of the IN stream.
  uint8_t *dp = xfr->buffer;
  int nrecvd = xfr->actual_length;

  // Update the circular buffer with the amount of data that we've received
  CommitData(nrecvd);

  if (!SigReceived()) {
    if (nrecvd > 0 && !SigReceived()) {
      uint32_t dropped = SigDetect(&sig_, dp, (uint32_t)nrecvd);

      // Consume stream signature, rather than propagating it to the output
      // side.
      if (SigReceived()) {
        SigProcess(sig_);
        dropped += sizeof(usbdev_stream_sig_t);
      }

      // Skip past any dropped bytes, including the signature, so that if there
      // are additional bytes we may process them.
      nrecvd = ((uint32_t)nrecvd > dropped) ? ((uint32_t)nrecvd - dropped) : 0;
      dp += dropped;

      if (dropped) {
        DiscardData(dropped);
      }
    }
  }

  bool ok = true;
  if (nrecvd > 0) {
    // Check the received LFSR-generated byte(s) and combine them with the
    // output of our host-side LFSR.
    ok = ProcessData(dp, nrecvd);
  }

  if (ok) {
    if (CanSchedule()) {
      // Attempt to set up another IN transfer.
      failed_ = !ServiceIN();
    } else {
      inActive_ = false;
    }
  } else {
    failed_ = true;
  }
}

// Callback function supplied to libusb for OUT transfers.
void USBDevInt::CallbackOUT(struct libusb_transfer *xfr) {
  if (xfr->status != LIBUSB_TRANSFER_COMPLETED) {
    std::cerr << PrefixID() << " Invalid/unexpected OUT transfer status "
              << xfr->status << std::endl;
    std::cerr << "length " << xfr->length << " actual " << xfr->actual_length
              << std::endl;
    failed_ = true;
    return;
  }

  if (verbose_) {
    std::cout << PrefixID() << "CallbackOUT xfr " << xfr << std::endl;
    DumpIntTransfer(xfr);
  }

  // Note: we're not expecting any truncation on OUT transfers.
  assert(xfr->actual_length == xfr->length);
  ConsumeData(xfr->actual_length);

  if (CanSchedule()) {
    // Attempt to set up another OUT transfer.
    failed_ = !ServiceOUT();
  } else {
    outActive_ = false;
  }
}
