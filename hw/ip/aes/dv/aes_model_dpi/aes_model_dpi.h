// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _AES_MODEL_DPI_H_
#define _AES_MODEL_DPI_H_

#include "svdpi.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Perform encryption/decryption of one block.
 *
 * @param  impl_i    Select reference impl.: 0 = C model, 1 = OpenSSL/BoringSSL
 * @param  mode_i    Operation mode: 0 = encryption, 1 = decryption
 * @param  key_len_i Key length: 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
 * @param  key_i     Full input key
 * @param  data_i    Input data
 * @param  data_o    Output data
 */
void aes_crypt_dpi(const unsigned char impl_i, const unsigned char mode_i,
                   const svBitVecVal *key_len_i, const svOpenArrayHandle key_i,
                   const svOpenArrayHandle data_i,
                   const svOpenArrayHandle data_o);

/**
 * Perform sub bytes operation during encryption/decryption.
 *
 * @param  mode_i Operation mode: 0 = encryption, 1 = decryption
 * @param  data_i Input data
 * @param  data_o Output data
 */
void aes_sub_bytes_dpi(const unsigned char mode_i,
                       const svOpenArrayHandle data_i,
                       const svOpenArrayHandle data_o);

/**
 * Perform shift rows operation during encryption/decryption.
 *
 * @param  mode_i Operation mode: 0 = encryption, 1 = decryption
 * @param  data_i Input data
 * @param  data_o Output data
 */
void aes_shift_rows_dpi(const unsigned char mode_i,
                        const svOpenArrayHandle data_i,
                        const svOpenArrayHandle data_o);

/**
 * Perform mix columns operation during encryption/decryption.
 *
 * @param  mode_i Operation mode: 0 = encryption, 1 = decryption
 * @param  data_i Input data
 * @param  data_o Output data
 */
void aes_mix_columns_dpi(const unsigned char mode_i,
                         const svOpenArrayHandle data_i,
                         const svOpenArrayHandle data_o);

/**
 * Generate full key for next round during encryption/decryption.
 *
 * @param  mode_i    Operation mode: 0 = encryption, 1 = decryption
 * @param  rcon_old  Previous rcon (updates intenally before being used)
 * @param  round_i   Round index
 * @param  key_len_i Key length: 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
 * @param  key_i     Full input key
 * @param  key_o     Full output key
 */
void aes_key_expand_dpi(const unsigned char mode_i, const svBitVecVal *rcon_old,
                        const svBitVecVal *round_i,
                        const svBitVecVal *key_len_i,
                        const svOpenArrayHandle key_i,
                        const svOpenArrayHandle key_o);

/**
 * Get data block from simulation.
 *
 * @param  data_i Input data from simulation
 * @return Pointer to data copied to memory, 0 in case of an error
 */
unsigned char *aes_data_get(const svOpenArrayHandle data_i);

/**
 * Write data block to simulation and free the source buffer afterwards.
 *
 * @param  data_o Output data for simulation
 * @param  data   Data to be copied to simulation, freed after the operation
 */
void aes_data_put(const svOpenArrayHandle data_o, unsigned char *data);

/**
 * Get key block from simulation.
 *
 * @param  key_i Input key from simulation
 * @return Pointer to key copied to memory, 0 in case of an error
 */
unsigned char *aes_key_get(const svOpenArrayHandle key_i);

/**
 * Write key block to simulation and free the source buffer afterwards.
 *
 * @param  key_o Output key for simulation
 * @param  key   Key to be copied to simulation, freed after the operation
 */
void aes_key_put(const svOpenArrayHandle key_o, unsigned char *key);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _AES_MODEL_DPI_H_
