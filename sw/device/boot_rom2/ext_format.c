// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/boot_rom2/ext_format.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/check.h"

/**
 * Convenience macro for checking if a condition is true and returning an error
 * if it isn't, along with a log statement.
 */
#define PARSE_CHECK(cond, ...)                        \
  do {                                                \
    if (!(cond)) {                                    \
      /* No log for now.                              \
      LOG_ERROR("Parse check-fail: " __VA_ARGS__); */ \
      return kExtParseUnspecifiedError;               \
    }                                                 \
  } while (false);

/**
 * Magic number at the start of every EXT binary.
 */
static const uint32_t kExtMagic = 0x5245544f; // ASCII: "OTER".

/**
 * Convenience struct for pulling out the fixed part of the executable header.
 */
typedef struct fixed_header {
  uint32_t magic, version, payload_len, entrypoint;
} fixed_header_t;

static ext_parse_result_t metadata_len_from_version(
    ext_format_version_t version, size_t *len_out) {
  switch (version) {
    case kExtFormatVersion0:
      *len_out = 0;
      return kExtParseOk;
    default:
      return kExtParseUnspecifiedError;
  }
}

ext_parse_result_t ext_parse_common(const uint8_t *binary,
                                    const ext_crypto_vt_t *crypto,
                                    ext_common_t *out) {
  fixed_header_t header;
  memcpy(&header, binary, sizeof(header));

  // Compute offset pointers into |binary| pointing to relevant fields within.
  const uint8_t *signature = binary + sizeof(header);
  const uint8_t *footer_hash = signature + crypto->sig_len;

  // Verify the magic word.
  PARSE_CHECK(header.magic == kExtMagic, "Magic value mismatch.");

  // Hash the executable header, for signature verification.
  const uint8_t *header_hash;
  PARSE_CHECK(crypto->hash_start(crypto->self), "Failed to start header hash.");
  PARSE_CHECK(
      crypto->hash_data(crypto->self, (const uint8_t *)&header, sizeof(header)),
      "Failed to hash the fixed header.");
  PARSE_CHECK(crypto->hash_data(crypto->self, footer_hash, crypto->hash_len),
              "Failed to hash the footer hash.");
  PARSE_CHECK(crypto->hash_finish(crypto->self, &header_hash),
              "Failed to complete header hash.");

  // Verify the header signature.
  PARSE_CHECK(crypto->verify_signature(crypto->self, header_hash, signature),
              "Failed to verify header signature.");

  // At this point, we can trust the header contents to do pointer arithmetic
  // with.
  const uint8_t *metadata = footer_hash + crypto->hash_len;
  size_t metadata_len;
  PARSE_CHECK(
      metadata_len_from_version(header.version, &metadata_len) == kExtParseOk,
      "Bad version number.");
  const uint8_t *payload = metadata + metadata_len;

  // Hash the footer (i.e., everything after the footer hash).
  const uint8_t *footer_hash_computed;
  PARSE_CHECK(crypto->hash_start(crypto->self), "Failed to start footer hash.");
  PARSE_CHECK(crypto->hash_data(crypto->self, metadata, metadata_len),
              "Failed to hash metadata.");
  PARSE_CHECK(crypto->hash_data(crypto->self, payload, header.payload_len),
              "Failed to hash payload.");
  PARSE_CHECK(crypto->hash_finish(crypto->self, &footer_hash_computed),
              "Failed to complete footer hash.");

  // NOTE: This comparison should probably be made constant-time, since we might
  // not want an attacker to learn how close a failed hash is.
  PARSE_CHECK(memcmp(footer_hash, footer_hash_computed, crypto->hash_len) == 0,
              "Footer hash mismatch.");

  // At this point, we have verified all cryptographic information within the
  // header, and can safely trust all the bytes therein (modulo glitching).

  *out = (ext_common_t){
      .payload = payload,
      .payload_len = header.payload_len,
      .metadata = metadata,
      .metadata_len = metadata_len,
      .entrypoint = (void *)(payload + header.entrypoint),
  };
  return kExtParseOk;
}

ext_parse_result_t ext_parse_v0(const ext_common_t *binary,
                                const ext_crypto_vt_t *crypto,
                                ext_metadata_v0_t *out) {
  // Nothing to do here, since there is no metadata information.
  return kExtParseOk;
}
