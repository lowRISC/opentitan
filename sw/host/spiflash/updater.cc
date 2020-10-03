// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/host/spiflash/updater.h"

#include <algorithm>
#include <assert.h>
#include <unistd.h>

namespace opentitan {
namespace spiflash {
namespace {

/**
 * Populate target frame `f`.
 *
 * Populates frame `f` with `frame_number`, `code_offset`, and frame data
 * starting at `code_offset` from `code` buffer. Calculates SHA256 hash of
 * frame payload and it stores it in the frame header.
 *
 * @return the number of bytes loaded into the frame.
 */
uint32_t Populate(uint32_t frame_number, uint32_t code_offset,
                  const std::string &code, Frame *f) {
  assert(f);
  assert(code_offset < code.size());

  // Populate payload data. Initialize buffer to 0xff to minimize flash
  // writes.
  size_t copy_size =
      std::min<size_t>(f->PayloadSize(), code.size() - code_offset);
  memset(f->data, 0xff, f->PayloadSize());
  memcpy(f->data, code.data() + code_offset, copy_size);

  // Populate header number, offset and hash.
  f->hdr.frame_num = frame_number;
  f->hdr.offset = code_offset;
  return copy_size;
}

/**
 * Calculate hash for frame `f` and store it in the frame header hash field.
 */
void HashFrame(Frame *f) {
  SHA256_CTX sha256;
  SHA256_Init(&sha256);
  SHA256_Update(&sha256, &f->hdr.frame_num, sizeof(f->hdr.frame_num));
  SHA256_Update(&sha256, &f->hdr.offset, sizeof(f->hdr.offset));
  SHA256_Update(&sha256, f->data, f->PayloadSize());
  SHA256_Final(f->hdr.hash, &sha256);
}

}  // namespace

bool Updater::Run() {
  std::cout << "Running SPI flash update." << std::endl;
  std::vector<Frame> frames;
  if (!GenerateFrames(options_.code, &frames)) {
    std::cerr << "Unable to process flash image." << std::endl;
    return false;
  }
  std::cout << "Image divided into " << frames.size() << " frames."
            << std::endl;

  std::string ack_expected;
  ack_expected.resize(sizeof(Frame), '\0');
  std::string ack;
  ack.resize(sizeof(Frame));
  for (uint32_t current_frame = 0; current_frame < frames.size();) {
    const Frame &f = frames[current_frame];

    std::cout << "frame: 0x" << std::setfill('0') << std::setw(8) << std::hex
              << f.hdr.frame_num << " to offset: 0x" << std::setfill('0')
              << std::setw(8) << std::hex << f.hdr.offset << std::endl;

    if (!spi_->TransmitFrame(reinterpret_cast<const uint8_t *>(&f),
                             sizeof(Frame))) {
      std::cerr << "Failed to transmit frame no: 0x" << std::setfill('0')
                << std::setw(8) << std::hex << f.hdr.frame_num << std::endl;
    }

    // After receiving and validating the first frame, the device is erasing
    // the Flash.
    if (current_frame == 0) {
      usleep(options_.flash_erase_delay_us);
    }

    // When we send each frame we wait for the correct hash before continuing.
    if (current_frame == frames.size() - 1 ||
        spi_->CheckHash(reinterpret_cast<const uint8_t *>(&f), sizeof(Frame))) {
      current_frame++;
    }
  }
  return true;
}

bool Updater::GenerateFrames(const std::string &code,
                             std::vector<Frame> *frames) {
  if (frames == nullptr) {
    return false;
  }
  uint32_t frame_number = 0;
  uint32_t code_offset = 0;
  while (code_offset < code.size()) {
    Frame frame;
    uint32_t bytes_copied = Populate(frame_number, code_offset, code, &frame);
    code_offset += bytes_copied;
    frame_number++;
    frames->emplace_back(frame);
  }
  // Update last frame to sentinel EOF value.
  Frame &last_frame = frames->back();
  last_frame.hdr.frame_num = 0x80000000 | last_frame.hdr.frame_num;

  for (Frame &f : *frames) {
    HashFrame(&f);
  }
  return true;
}

}  // namespace spiflash
}  // namespace opentitan
