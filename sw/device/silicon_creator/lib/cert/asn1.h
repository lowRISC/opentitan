// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_ASN1_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_ASN1_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Structure holding the state of the asn1 generator.
 *
 * The fields in this structure should be considered
 * private and not be read or written directly.
 */
typedef struct asn1_state {
  // Buffer containing the output.
  uint8_t *buffer;
  // Size of the output buffer.
  size_t size;
  // Current offset in the output.
  size_t offset;
  // Tracking the last active error.
  // When there is an active error, all operations other than `asn1_start`,
  // `asn1_finish` and `asn1_clear_error` will be no-op.
  rom_error_t error;
} asn1_state_t;

/**
 * Clear the ASN1 builder active error in the `state`.
 *
 * @param[out] state Pointer to a user-allocated state to be cleared.
 */
void asn1_clear_error(asn1_state_t *state);

/**
 * Start generating an ASN1 stream.
 *
 * @param[out] new_state Pointer to a user-allocated state to be initialized.
 * @param buffer Pointer to a user-provided buffer.
 * @param size Size of the user-provided buffer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t asn1_start(asn1_state_t *new_state, uint8_t *buffer, size_t size);

/**
 * Finish an ASN1 stream and return the size.
 *
 * Note: the state will be cleared out after this call.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param[out] out_size Pointer to an integer that will be set to the size of
 * the stream.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t asn1_finish(asn1_state_t *state, size_t *out_size);

/**
 * Push a byte into the ASN1 buffer.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the initialized by asn1_start.
 * @param byte Byte to add to the buffer.
 */
void asn1_push_byte(asn1_state_t *state, uint8_t byte);

/**
 * Push bytes into the ASN1 buffer.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the initialized by asn1_start.
 * @param bytes Pointer to an array of bytes.
 * @param size Number of bytes in the array.
 */
void asn1_push_bytes(asn1_state_t *state, const uint8_t *bytes, size_t size);

/**
 * Structure holding the information about an unfinished tag sequence.
 *
 * The fields in this structure should be considered
 * private and not be read or written directly.
 */
typedef struct asn1_tag {
  // Pointer to state.
  asn1_state_t *state;
  // Offset of the start of the length octets.
  size_t len_offset;
  // How many bytes were allocated for the length octets.
  size_t len_size;
} asn1_tag_t;

/**
 * Structure holding the information about an unfinished bistring.
 *
 * The fields in this structure should be considered
 * private and not be read or written directly.
 */
typedef struct asn1_bitstring {
  // Pointer to state.
  asn1_state_t *state;
  // Offset of the "unused bits" byte.
  size_t unused_bits_offset;
  // How many bits have been added to the current byte (between 0 and 7).
  size_t used_bits;
  // Current value of the last byte of the string.
  uint8_t current_byte;
} asn1_bitstring_t;

// ASN1 tag classes.
typedef enum asn1_tag_class {
  kAsn1TagClassUniversal = 0 << 6,
  kAsn1TagClassApplication = 1 << 6,
  kAsn1TagClassContext = 2 << 6,
  kAsn1TagClassPrivate = 3 << 6,
} asn1_tag_class_t;

// ASN1 tag primitive/constructed bit.
typedef enum asn1_tag_form {
  kAsn1TagFormPrimitive = 0 << 5,
  kAsn1TagFormConstructed = 1 << 5,
} asn1_tag_form_t;

// ASN1 tag number (for universal tags).
typedef enum asn1_tag_number {
  kAsn1TagNumberBoolean = 0x01,
  kAsn1TagNumberInteger = 0x02,
  kAsn1TagNumberBitString = 0x03,
  kAsn1TagNumberOctetString = 0x04,
  kAsn1TagNumberOid = 0x06,
  kAsn1TagNumberUtf8String = 0x0c,
  kAsn1TagNumberPrintableString = 0x13,
  kAsn1TagNumberGeneralizedTime = 0x18,
  kAsn1TagNumberSequence = 0x30,
  kAsn1TagNumberSet = 0x31,
} asn1_tag_number_t;

/**
 * Start an ASN1 tag.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param[out] new_tag Pointer to a user-allocated tag to be initialized.
 * @param id Identifier byte of the tag (see ASN1_CLASS_*, ASN1_FORM_* and
 * ASN1_TAG_*).
 */
void asn1_start_tag(asn1_state_t *state, asn1_tag_t *new_tag, uint8_t id);

/**
 * Finish an ASN1 tag.
 *
 * If size hint provided to asn1_start_tag does not match the actual size
 * of the data, this function will fix it up, potentially at the cost of moving
 * bytes within the buffer.
 *
 * Note: the `tag` will be cleared out after this call.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param tag Pointer to the tag initialized by asn1_start_tag.
 */
void asn1_finish_tag(asn1_tag_t *tag);

/**
 * Push a tagged boolean into the buffer.
 *
 * Note: this function will encode true as 0xff (any non-zero value is
 * acceptable per the specification).
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param tag Identifier octet of the tag.
 * @param value Boolean value.
 */
void asn1_push_bool(asn1_state_t *state, uint8_t tag, bool value);

/**
 * Push a tagged integer into the buffer.
 *
 * This function allows the caller to set the tag to a non-standard value which
 * can be useful for IMPLICIT integers. Use ASN1_TAG_INTEGER for standard
 * integers.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param tag Identifier octet of the tag.
 * @param value Integer value.
 */
void asn1_push_int32(asn1_state_t *state, uint8_t tag, int32_t value);

/**
 * See asn1_push_int32()
 */
void asn1_push_uint32(asn1_state_t *state, uint8_t tag, uint32_t value);

/**
 * Push a tagged integer into the buffer.
 *
 * This function allows the caller to set the tag to a non-standard value which
 * can be useful for IMPLICIT integers. Use ASN1_TAG_INTEGER for standard
 * integers.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param tag Identifier octet of the tag.
 * @param is_signed If true, the byte array represents a signed integer in two's
 * complement.
 * @param bytes_be Pointer to a byte array holding an integer in big-endian
 * format.
 * @param size Number of the bytes in the array.
 */
void asn1_push_integer(asn1_state_t *state, uint8_t tag, bool is_signed,
                       const uint8_t *bytes_be, size_t size);

/**
 * Push a padded integer into the buffer.
 *
 * If the integer is unsigned, it will be padded to the required length with
 * zeroes. If the integer is signed, it will be padded so as to preserve its
 * value in two's complement. If the integer size is larger than the requested
 * size with padding, an error will be reported.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param is_signed If true, the byte array represents a signed integer in two's
 * complement.
 * @param bytes_be Pointer to a byte array holding an integer in big-endian
 * format.
 * @param size Number of the bytes in the array.
 * @param size Number of the bytes to output with padding.
 */
void asn1_push_integer_pad(asn1_state_t *state, bool is_signed,
                           const uint8_t *bytes_be, size_t size,
                           size_t padded_size);

/**
 * Push an object identifier into the buffer.
 *
 * The object identifier must already be encoded according to the X.690 spec,
 * section 8.19 (https://www.itu.int/rec/T-REC-X.690).
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param bytes Pointer to a byte array holding the object identifier.
 * @param size Number of the bytes in the array.
 */
void asn1_push_oid_raw(asn1_state_t *state, const uint8_t *bytes, size_t size);

/**
 * Push a tagged string into the buffer.
 *
 * This function allows the caller to set the tag to a non-standard value which
 * can be useful for IMPLICIT strings. Use ASN1_TAG_PRINTABLE_STRING or
 * ASN1_TAG_UTF8_STRING for standard strings. It is the responsability of the
 * caller to make sure that the provided string does not contain invalid
 * characters for the selected encoding. This function will stop at the first 0
 * in the string or after processing the provided number of characters,
 * whichever comes first.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param tag Identifier octet of the tag.
 * @param str Pointer to a (not necessarily zero-terminated) string.
 * @param max_len Maximum number of characters to read from the string.
 */
void asn1_push_string(asn1_state_t *state, uint8_t tag, const char *str,
                      size_t max_len);

/**
 * Push a tagged hexstring into the buffer.
 *
 * This function allows the caller to set the tag to a non-standard value which
 * can be useful for IMPLICIT strings. This function takes an array of bytes
 * and output exactly two lowercase hex characters per byte in the input buffer.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param tag Identifier octet of the tag.
 * @param str Pointer to a byte array.
 * @param size Number of the bytes in the array.
 */
void asn1_push_hexstring(asn1_state_t *state, uint8_t tag, const uint8_t *bytes,
                         size_t size);

/**
 * Start an ASN1 bitstring.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param state Pointer to the state initialized by asn1_start.
 * @param[out] out_bitstring Pointer to a user-allocated bitstring to be
 * initialized.
 */
void asn1_start_bitstring(asn1_state_t *state, asn1_bitstring_t *out_bitstring);

/** Add a bit to a bitstring.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param bitstring Pointer to a bitstring initialized by asn1_start_bitstring.
 * @param bit Bit to add at the end of the string.
 */
void asn1_bitstring_push_bit(asn1_bitstring_t *bitstring, bool bit);

/** Finish an ASN1 bitstring.
 *
 * Note: This function tracks its error in the asn1 state, and the error will
 * be returned by `asn1_finish` in the end. This function will be no-op when
 * the state has an active error.
 *
 * @param bitstring Pointer to a bitstring initialized by asn1_start_bitstring.
 */
void asn1_finish_bitstring(asn1_bitstring_t *bitstring);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_ASN1_H_
