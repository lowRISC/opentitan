// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_PRIM_DV_PRIM_RAM_SCR_CPP_SCRAMBLE_MODEL_H_
#define OPENTITAN_HW_IP_PRIM_DV_PRIM_RAM_SCR_CPP_SCRAMBLE_MODEL_H_

#include <stdint.h>
#include <vector>

const uint32_t kPrinceWidth = 64;
const uint32_t kPrinceWidthByte = kPrinceWidth / 8;

// C++ model of memory scrambling. All byte vectors are in little endian byte
// order (least significant byte at index 0).

/** Scramble an address to give the physical address used to access the
 * scrambled memory. Return vector of scrambled address bytes
 *
 * @param addr_in      Byte vector of address
 * @param addr_width   Width of the address in bits
 * @param nonce        Byte vector of scrambling nonce
 * @param nonce_width  Width of scramble nonce in bits
 * @return Byte vector with scrambled address
 */
std::vector<uint8_t> scramble_addr(const std::vector<uint8_t> &addr_in,
                                   uint32_t addr_width,
                                   const std::vector<uint8_t> &nonce,
                                   uint32_t nonce_width);

/** Decrypt scrambled data
 * @param data_in          Byte vector of data to decrypt
 * @param data_width       Width of data in bits
 * @param subst_perm_width Width over which the substitution/permutation network
 *                         is applied (DiffWidth parameter on prim_ram_1p_scr)
 * @param addr             Byte vector of data address
 * @param addr_width       Width of the address in bits
 * @param nonce            Byte vector of scrambling nonce
 * @param key              Byte vector of scrambling key
 * @param repeat_keystream Repeat the keystream of one single PRINCE instance if
 *                         set to true. Otherwise multiple PRINCE instances are
 *                         used.
 * @return Byte vector with decrypted data
 */
std::vector<uint8_t> scramble_decrypt_data(
    const std::vector<uint8_t> &data_in, uint32_t data_width,
    uint32_t subst_perm_width, const std::vector<uint8_t> &addr,
    uint32_t addr_width, const std::vector<uint8_t> &nonce,
    const std::vector<uint8_t> &key, bool repeat_keystream);

/** Encrypt scrambled data
 * @param data_in          Byte vector of data to encrypt
 * @param data_width       Width of data in bits
 * @param subst_perm_width Width over which the substitution/permutation network
 *                         is applied (DiffWidth parameter on prim_ram_1p_scr)
 * @param addr             Byte vector of data address
 * @param addr_width       Width of the address in bits
 * @param nonce            Byte vector of scrambling nonce
 * @param key              Byte vector of scrambling key
 * @param repeat_keystream Repeat the keystream of one single PRINCE instance if
 *                         set to true. Otherwise multiple PRINCE instances are
 *                         used.
 * @return Byte vector with encrypted data
 */
std::vector<uint8_t> scramble_encrypt_data(
    const std::vector<uint8_t> &data_in, uint32_t data_width,
    uint32_t subst_perm_width, const std::vector<uint8_t> &addr,
    uint32_t addr_width, const std::vector<uint8_t> &nonce,
    const std::vector<uint8_t> &key, bool repeat_keystream);

#endif  // OPENTITAN_HW_IP_PRIM_DV_PRIM_RAM_SCR_CPP_SCRAMBLE_MODEL_H_
