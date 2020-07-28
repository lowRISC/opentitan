// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_DV_AES_MODEL_DPI_AES_MODEL_DPI_H_
#define OPENTITAN_HW_IP_AES_DV_AES_MODEL_DPI_AES_MODEL_DPI_H_

#include "svdpi.h"

#ifdef __cplusplus
extern "C" {
#endif

// Masks for ignoring unused bits in data passed from the simulator (their value
// is undetermined).
#define impl_mask 0x1
#define op_mask 0x1
#define mode_mask 0x3F
#define key_len_mask 0x7
#define rcon_mask 0xFF
#define round_mask 0xF

/**
 * Perform encryption/decryption of one block.
 *
 * @param  impl_i    Select reference impl.: 0 = C model, 1 = OpenSSL/BoringSSL
 * @param  op_i      Operation: 0 = encrypt, 1 = decrypt
 * @param  mode_i    Cipher mode: 6'b00_0001 = ECB, 6'00_b0010 = CBC,
 *                                6'b00_0100 = CFB, 6'b00_1000 = OFB,
 *                                6'b01_0000 = CTR, 6'b10_0000 = NONE
 * @param  iv_i      Initialization vector: 2D matrix (3D packed array in SV)
 * @param  key_len_i Key length: 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
 * @param  key_i     Full input key, 1D array of words (2D packed array in SV)
 * @param  data_i    Input data, 2D state matrix (3D packed array in SV)
 * @param  data_o    Output data, 2D state matrix (3D packed array in SV)
 */
void c_dpi_aes_crypt_block(const unsigned char impl_i, const unsigned char op_i,
                           const svBitVecVal *mode_i, const svBitVecVal *iv_i,
                           const svBitVecVal *key_len_i,
                           const svBitVecVal *key_i, const svBitVecVal *data_i,
                           svBitVecVal *data_o);

/**
 * Perform encryption/decryption of an entire message using OpenSSL/BoringSSL.
 *
 * @param  impl_i    Select reference impl.: 0 = C model, 1 = OpenSSL/BoringSSL
 * @param  op_i      Operation: 0 = encrypt, 1 = decrypt
 * @param  mode_i    Cipher mode: 6'b00_0001 = ECB, 6'00_b0010 = CBC,
 *                                6'b00_0100 = CFB, 6'b00_1000 = OFB,
 *                                6'b01_0000 = CTR, 6'b10_0000 = NONE
 * @param  iv_i      Initialization vector: 1D array of words (2D packed array
 *                   in SV)
 * @param  key_len_i Key length: 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
 * @param  key_i     Full input key, 1D array of words (2D packed array in SV)
 * @param  data_i    Input data, 1D byte array (open array in SV)
 * @param  data_o    Output data, 1D byte array (open array in SV)
 */
void c_dpi_aes_crypt_message(unsigned char impl_i, unsigned char op_i,
                             const svBitVecVal *mode_i, const svBitVecVal *iv_i,
                             const svBitVecVal *key_len_i,
                             const svBitVecVal *key_i,
                             const svOpenArrayHandle data_i,
                             svOpenArrayHandle data_o);

/**
 * Perform sub bytes operation for forward/inverse cipher operation.
 *
 * @param  op_i   Cipher operation: 0 = forward, 1 = inverse
 * @param  data_i Input data
 * @param  data_o Output data
 */
void c_dpi_aes_sub_bytes(const unsigned char op_i, const svBitVecVal *data_i,
                         svBitVecVal *data_o);

/**
 * Perform shift rows operation for forward/inverse cipher operation.
 *
 * @param  op_i   Cipher operation: 0 = forward, 1 = inverse
 * @param  data_i Input data
 * @param  data_o Output data
 */
void c_dpi_aes_shift_rows(const unsigned char op_i, const svBitVecVal *data_i,
                          svBitVecVal *data_o);

/**
 * Perform mix columns operation for forward/inverse cipher operation.
 *
 * @param  op_i   Cipher operation: 0 = forward, 1 = inverse
 * @param  data_i Input data
 * @param  data_o Output data
 */
void c_dpi_aes_mix_columns(const unsigned char op_i, const svBitVecVal *data_i,
                           svBitVecVal *data_o);

/**
 * Generate full key for next round for forward/inverse cipher operation.
 *
 * @param  op_i      Cipher operation: 0 = forward, 1 = inverse
 * @param  rcon_old  Previous rcon (updates intenally before being used)
 * @param  round_i   Round index
 * @param  key_len_i Key length: 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
 * @param  key_i     Full input key
 * @param  key_o     Full output key
 */
void c_dpi_aes_key_expand(const unsigned char op_i, const svBitVecVal *rcon_i,
                          const svBitVecVal *round_i,
                          const svBitVecVal *key_len_i,
                          const svBitVecVal *key_i, svBitVecVal *key_o);

/**
 * Get packed data block from simulation.
 *
 * @param  data_i Input data from simulation
 * @return Pointer to data copied to memory, 0 in case of an error
 */
unsigned char *aes_data_get(const svBitVecVal *data_i);

/**
 * Write packed data block to simulation and free the source buffer afterwards.
 *
 * @param  data_o Output data for simulation
 * @param  data   Data to be copied to simulation, freed after the operation
 */
void aes_data_put(svBitVecVal *data_o, unsigned char *data);

/**
 * Get unpacked data from simulation.
 *
 * @param  data_i Input data from simulation
 * @return Pointer to data copied to memory, 0 in case of an error
 */
unsigned char *aes_data_unpacked_get(const svOpenArrayHandle data_i);

/**
 * Write unpacked data to simulation and free the source buffer
 * afterwards.
 *
 * @param  data_o Output data for simulation
 * @param  data   Data to be copied to simulation, freed after the operation
 */
void aes_data_unpacked_put(const svOpenArrayHandle data_o, unsigned char *data);

/**
 * Get packed key block from simulation.
 *
 * @param  key_i Input key from simulation
 * @return Pointer to key copied to memory, 0 in case of an error
 */
unsigned char *aes_key_get(const svBitVecVal *key_i);

/**
 * Write packed key block to simulation and free the source buffer afterwards.
 *
 * @param  key_o Output key for simulation
 * @param  key   Key to be copied to simulation, freed after the operation
 */
void aes_key_put(svBitVecVal *key_o, unsigned char *key);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // OPENTITAN_HW_IP_AES_DV_AES_MODEL_DPI_AES_MODEL_DPI_H_
