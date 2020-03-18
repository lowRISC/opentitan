// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_BOOT_ROM2_EXT_FORMAT_H_
#define OPENTITAN_SW_DEVICE_BOOT_ROM2_EXT_FORMAT_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * Parsing library for the ROM_EXT executable format.
 *
 * The ROM_EXT format consists of three parts: a fixed header, a variable
 * metadata region, and a payload. A ROM_EXT is encoded as the unaligned[1]
 * concatenation of these three parts:
 *   struct rom_ext {
 *     rom_ext_header header;
 *     rom_ext_metadata<header.version> meta;
 *     uint8_t payload[header.payload_len];
 *   };
 *
 * The fixed header consists of four words and two cryptographic measurements.
 *   struct rom_ext_header {
 *     uint32_t magic, version, payload_len, entrypoint;
 *     uint8_t signature[crypto.sig_len];
 *     uint8_t footer_hash[crypto.hash_len];
 *   };
 *
 * The fields are as follows:
 * - |magic| is always the value 0x5245544f ("OTER", OpenTitan Ext Rom).
 * - |version| is a |ext_format_version_t|, which determines the layout (and, as
 *   such, length) of |rom_ext_metadata<version>|.
 * - |paylaod_len| is the length of tha payload, in bytes.
 * - |entrypoint| is used to compute the program entry point, which is equal
 *   to |&payload[entrypoint]|.
 * - |signature| is a cryptographic signature of the following value (where ++
 *   is concatenation):
 *     magic ++ version ++ payload_len ++ entrypoint ++ footer_hash
 *   The algorithm and key are unspecified, and are an otherwise pluggable
 *   component. This signature (along with |footer_hash|) authenticates the
 *   entire contents of the binary, in a way which can be verified without
 *   needing to trust unauthenticates lengths.
 * - |footer_hash| is a cryptographic hash of the value |metadata ++ payload|,
 *   using a known but unspecified algorithm.
 *
 * rom_ext_metadata<version> is a variable-length struct, whose length is
 * determined by the value of |version|. This allows the format to change over
 * time, while also providing an explicit versioning boundary. The contents and
 * encodings of each metadata version are specified in their specific structs.
 *
 * It is recommended to use this library as follows:
 *   uint8_t *binary = &some_global;
 *   ext_crypto_vt_t *crypto = &some_other_global;
 *
 *   ext_common_t parsed_binary;
 *   CHECK(ext_parse_common(binary, crypto, &parsed_binary) == kExtParseOk);
 *   // NOTE: we *do not* read the version number from |binary| ourselves!
 *   switch (parsed_binary.version) {
 *     case kExtFormatVersion5: {
 *       ext_metadata_v5_t meta;
 *       CHECK(ext_parse_v5(&parsed_binary, crypto, &meta) == kExtParseOk);
 *       // v5-specific checks.
 *       break;
 *     }
 *     case kExtFormatVersion7: {
 *       ext_metadata_v7_t meta;
 *       CHECK(ext_parse_v7(&parsed_binary, crypto, &meta) == kExtParseOk);
 *       // v7-specific checks.
 *       break;
 *     }
 *     // Treat all versions we don't explicitly accept as a fatal error.
 *     default: LOG_FATAL("Found unacceptable version);
 *   }
 *
 *   // Other checks...
 *   final_jump(parsed_binary.entrypoint);
 *
 * This usage guarantees that only parsing subroutines for unsupported versions
 * are linked in, while ensuring that no control flow occurs using
 * unauthenticated lengths or version numbers.
 *
 * Functions in this header are guaranteed to return successfully (assuming this
 * if any functions passed in through a vtable). However, return codes many
 * indicate cryptographic state failure, and as such all parse failures should
 * be treated as if the binary were irreparably corrupted. An A/B update scheme
 * might prefer to fail over to the alternate B partition even if parsing A
 * fails in any way.
 *
 * [1] Alignment of all datatypes is to be ignored, and no padding is to be
 * inserted anywhere.
 */

/**
 * Represents a ROM_EXT format version.
 *
 * The actual integer value of each variant is the corresponding encoded value
 * for that version.
 */
typedef enum ext_format_version {
  /**
   * The trivial zeroth version, which has no extra metadata.
   */
  kExtFormatVersion0 = 0x0,
} ext_format_version_t;

/**
 * A vtable for supplying cryptographic primitives to a format parser.
 *
 * The documentation on contained function pointers describes what an
 * implementation of the vtable should do for that call. Functions should not
 * return until the operation they are peforming completes, and signaling
 * failure will be interpreted as a fatal parse error.
 *
 * It is recommended that values of this struct be declared as const globals, so
 * that they wind up in .rodata, and can be passed around as pointers to flash.
 */
typedef struct ext_crypto_vt {
  /**
   * Vtable "instance data", which is passed into virtual functions.
   *
   * This might hold, for example, pointers to DIF handles, or some kind of
   * handle to key material.
   */
  void *self;
  /**
   * Begins a hashing operation. This invalidates all previous hashing
   * operations, and allows |hash_data| to be called.
   *
   * @param self the self pointer.
   * @return true if the operation succeeded.
   */
  bool (*hash_start)(void *self);
  /**
   * Adds the contents of the buffer |data| (of length |len|) to the current
   * hashing operation.
   *
   * |hash_start| should be called before calling this function.
   *
   * @param self the self pointer.
   * @param data a buffer of data to be hashed.
   * @param len the length of the buffer.
   * @return true if the operation succeeded.
   */
  bool (*hash_data)(void *self, const uint8_t *data, size_t len);
  /**
   * Finishes the current hashing operation, returning the hash through an
   * unowned pointer.
   *
   * |hash_start| and |hash_data| should be called before calling this function.
   *
   * The pointer returned in |hash_out| is owned by the vtable implementation.
   * The implementation is allowed to re-use this buffer, which is to be
   * considered invalid upon the next call to |hash_finish|.
   *
   * @param self the self pointer.
   * @param hash_out the returned hash.
   */
  bool (*hash_finish)(void *self, const uint8_t **hash_out);

  /**
   * Performs a signature verification using an unspeficied public key.
   *
   * |hash| should be a hash of the same type as computed by |hash_finish()|,
   * and |signature| should be a corresponding signature. These buffers are of
   * fixed sized, and as such the implementation should be aware of their
   * lengths.
   *
   * The key used is unspecified and should be provided as part of |self|; this
   * function is merely a verification oracle for that particular key.
   *
   * Note that this function can return false on either signature mismatch or if
   * some other error occurs; these cases are not distinguished.
   *
   * @param self the self pointer.
   * @param hash a hash of the signed data.
   * @param signature the signature to verify the hash against.
   * @return true if the signature was successfully verified.
   */
  bool (*verify_signature)(void *self, const uint8_t *hash,
                           const uint8_t *signature);
  /**
   * The length of a hash, in bytes. This is used for computing offsets that
   * involve a hash value.
   */
  size_t hash_len;
  /**
   * The length of a signature, in bytes. This is used for computing offsets
   * that involve a signature value.
   */
  size_t sig_len;

  /**
   * Set to true if this vtable packs post-quantum cryptographic primitives.
   *
   * This currently does nothing, but may be used to compute alternate offsets
   * to a PQ signature.
   */
  bool is_post_quantum;
  // TODO: This is probably the correct place to indicate that we are requesting
  // PQ parsing... somehow.
} ext_crypto_vt_t;

/**
 * Represents the susccess state of a parse operation.
 *
 * This enum does not provide differentiated variants for different error types;
 * the exact kind of failure is intentionally unspefified.
 */
typedef enum ext_parse_result {
  kExtParseOk = 0,
  kExtParseUnspecifiedError,
} ext_parse_result_t;

/**
 * A struct containing all non-version-specific information parsed out of a
 * binary.
 *
 * This struct does not include signature information, which is already verified
 * at this point.
 */
typedef struct ext_common {
  /**
   * The version number extracted from binary.
   */
  ext_format_version_t version;
  /**
   * Absolute address of the start of the metadata region.
   */
  const uint8_t *metadata;
  /**
   * Length of the metadata region.
   */
  size_t metadata_len;
  /**
   * Absolute address of the start of the payload region.
   */
  const uint8_t *payload;
  /**
   * Length of the payload region.
   */
  size_t payload_len;
  /**
   * Absolute address of the next stage entrypoint.
   */
  void *entrypoint;
} ext_common_t;

/**
 * Peforms the "common" portion of a ROM_EXT binary, mostly consisting of
 * signature verification.
 *
 * @param binary a pointer to a valid ROM_EXT binary of any version.
 * @param crypto cryptographic primitives to use for parsing.
 * @param out out-param for the parsed binary.
 * @return whether the parse was successful.
 */
ext_parse_result_t ext_parse_common(const uint8_t *binary,
                                    const ext_crypto_vt_t *crypto,
                                    ext_common_t *out);

/**
 * Metadata value for the ROM_EXT-v0 format.
 *
 * This format is completely trivial. It has a length of zero and no encoding
 * whatsoever.
 */
typedef struct ext_metadata_v0 {
} ext_metadata_v0_t;

/**
 * Attempts to parse |binary| as a ROM_EXT-v0 binary.
 *
 * @param binary a pointer to a valid ROM_EXT-v0 binary.
 * @param crypto cryptographic primitives to use for parsing.
 * @param out out-param for the parsed metatdata.
 * @return whether the parse was successful.
 */
ext_parse_result_t ext_parse_v0(const ext_common_t *binary,
                                const ext_crypto_vt_t *crypto,
                                ext_metadata_v0_t *out);

#endif  // OPENTITAN_SW_DEVICE_BOOT_ROM2_EXT_FORMAT_H_
