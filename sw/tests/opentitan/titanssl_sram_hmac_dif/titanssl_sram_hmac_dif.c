// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_aes.h"  
#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/silicon_creator/rom/string_lib.h"

#include "hmac_regs.h"  // Generated.
#include "aes_regs.h"  // Generated.


#define TARGET_SYNTHESIS


typedef struct
{
    uint8_t *data;
    size_t n;
} titanssl_buffer_t;


static titanssl_buffer_t titanssl_data_src;
static titanssl_buffer_t titanssl_data_dst;
static titanssl_buffer_t titanssl_data_key;
static titanssl_buffer_t titanssl_data_iv;


/* ============================================================================
 * Benchmark setup
 * ========================================================================= */

// Configure debug mode.
#define TITANSSL_BENCHMARK_DEBUG 1

// Configure memory.
#define TITANSSL_BENCHMARK_L3 1
#define TITANSSL_BENCHMARK_L1 0

// Configure payload size.
#define TITANSSL_BENCHMARK_PAYLOAD_2354  1
#define TITANSSL_BENCHMARK_PAYLOAD_65536 0

// Configure cryptographic operation.
#define TITANSSL_BENCHMARK_SHA256 0
#define TITANSSL_BENCHMARK_HMAC   0
#define TITANSSL_BENCHMARK_AES    1

/* ============================================================================
 * Benchmark automatic configuration
 * ========================================================================= */

#if TITANSSL_BENCHMARK_L3
#define TITANSSL_DATA_SRC 0x80720000
#define TITANSSL_DATA_DST 0x80740000
#define TITANSSL_DATA_KEY 0xe0006000
#define TITANSSL_DATA_IV  0xe0006100
#elif TITANSSL_BENCHMARK_L1
#define TITANSSL_DATA_SRC 0xe0002000
#define TITANSSL_DATA_DST 0xe0004000
#define TITANSSL_DATA_KEY 0xe0006000
#define TITANSSL_DATA_IV  0xe0006100
#else
#error "Wrong benchmark memory configuration"
#endif

#if TITANSSL_BENCHMARK_PAYLOAD_2354
#define TITANSSL_PAYLOAD_SIZE 2354
#elif TITANSSL_BENCHMARK_PAYLOAD_65536
#define TITANSSL_PAYLOAD_SIZE 65536
#else
#error "Wrong benchmark payload configuration"
#endif

#if TITANSSL_BENCHMARK_SHA256

#define TITANSSL_OUTPUT_SIZE 32
#define TITANSSL_KEY_SIZE 0
#define TITANSSL_IV_SIZE 0
#define titanssl_benchmark titanssl_benchmark_hmac

#elif TITANSSL_BENCHMARK_HMAC

#define TITANSSL_OUTPUT_SIZE 32
#define TITANSSL_KEY_SIZE 32
#define TITANSSL_IV_SIZE 0
#define titanssl_benchmark titanssl_benchmark_hmac

#elif TITANSSL_BENCHMARK_AES

#define TITANSSL_OUTPUT_SIZE ((TITANSSL_PAYLOAD_SIZE+0xF) & ~0xF)
#define TITANSSL_KEY_SIZE 32
#define TITANSSL_IV_SIZE 16
#define titanssl_benchmark titanssl_benchmark_aes

#else
#error "Wrong benchmark operation configuration"
#endif

/* ============================================================================
 * Benchmark implementation
 * ========================================================================= */

void initialize_edn()
{
    uint32_t *p;

    p = (uint32_t*)0xc1160024;
    *p = 0x00909099;
    p = (uint32_t*)0xc1160020;
    *p = 0x00000006;
    p = (uint32_t*)0xc1150014;
    *p = 0x00000666;
    p = (uint32_t*)0xc1170014;
    *p = 0x00009966;
}

void initialize_memory(
        uint8_t *src_data,
        size_t src_n,
        uint8_t *dst_data,
        size_t dst_n,
        uint8_t *key_data,
        size_t key_n,
        uint8_t *iv_data,
        size_t iv_n)
{
    titanssl_data_src.data = src_data;
    titanssl_data_src.n = src_n;
    for (size_t i=0; i<src_n; i++) titanssl_data_src.data[i] = 0x0;

    titanssl_data_dst.data = dst_data;
    titanssl_data_dst.n = dst_n;
    for (size_t i=0; i<dst_n; i++) titanssl_data_dst.data[i] = 0x0;

    titanssl_data_key.data = key_data;
    titanssl_data_key.n = key_n;
    for (size_t i=0; i<key_n; i++) titanssl_data_key.data[i] = 0x0;

    titanssl_data_iv.data = iv_data;
    titanssl_data_iv.n = iv_n;
    for (size_t i=0; i<iv_n; i++) titanssl_data_iv.data[i] = 0x0;
}

void titanssl_benchmark_hmac(
        titanssl_buffer_t *const src,
        titanssl_buffer_t *const dst,
        titanssl_buffer_t *const key,
        __attribute__((unused)) titanssl_buffer_t *const iv)
{
    mmio_region_t hmac;
    uint32_t reg;
    const uint8_t *dp;

    // Get the HMAC IP base address
    hmac = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);

    // Initialize HMAC IP with digest and message in little-endian mode
    reg = mmio_region_read32(hmac, HMAC_CFG_REG_OFFSET);
#if TITANSSL_BENCHMARK_SHA256
    reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
    reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
    mmio_region_write32(hmac, HMAC_CFG_REG_OFFSET, reg);
#elif TITANSSL_BENCHMARK_HMAC
    mmio_region_write32(hmac, HMAC_KEY_0_REG_OFFSET, key->data[0]);
    mmio_region_write32(hmac, HMAC_KEY_1_REG_OFFSET, key->data[1]);
    mmio_region_write32(hmac, HMAC_KEY_2_REG_OFFSET, key->data[2]);
    mmio_region_write32(hmac, HMAC_KEY_3_REG_OFFSET, key->data[3]);
    mmio_region_write32(hmac, HMAC_KEY_4_REG_OFFSET, key->data[4]);
    mmio_region_write32(hmac, HMAC_KEY_5_REG_OFFSET, key->data[5]);
    mmio_region_write32(hmac, HMAC_KEY_6_REG_OFFSET, key->data[6]);
    mmio_region_write32(hmac, HMAC_KEY_7_REG_OFFSET, key->data[7]);
    reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
    reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, true);
    mmio_region_write32(hmac, HMAC_CFG_REG_OFFSET, reg);
#endif

    // Start operations
    mmio_region_nonatomic_set_bit32(hmac, HMAC_CMD_REG_OFFSET, HMAC_CMD_HASH_START_BIT);

    // Compute SHA256, assuming the payload address is 4-bytes aligned
    dp = src->data;
    while (dp < src->data + src->n) 
    {
        uint32_t n_bytes;
        uint32_t n_words;

        // Compute how many bytes need will be pushed into the accelerator FIFO.
        n_bytes = 16 * sizeof(uint32_t);
        if (n_bytes > src->data + src->n - dp) n_bytes = src->data + src->n - dp;
        n_words = n_bytes >> 2;
        n_bytes = n_bytes & 0x3;

        // Wait for the accelerator fifo to be empty.
        while(!mmio_region_get_bit32(hmac, HMAC_STATUS_REG_OFFSET, HMAC_STATUS_FIFO_EMPTY_BIT));

        // Push data into the FIFO.
        for (size_t i=0; i<n_words; i++)
        {
            mmio_region_write32(hmac, HMAC_MSG_FIFO_REG_OFFSET, *(uint32_t*)dp);
            dp += sizeof(uint32_t);
        }
        for (size_t i=0; i<n_bytes; i++)
        {
            mmio_region_write8(hmac, HMAC_MSG_FIFO_REG_OFFSET, *dp);
            dp += 1;
        }
    }
    mmio_region_nonatomic_set_bit32(hmac, HMAC_CMD_REG_OFFSET, HMAC_CMD_HASH_PROCESS_BIT);

    // Wait for SHA-256 completion
    while (!mmio_region_get_bit32(hmac, HMAC_INTR_STATE_REG_OFFSET, HMAC_INTR_STATE_HMAC_DONE_BIT));
    mmio_region_nonatomic_set_bit32(hmac, HMAC_INTR_STATE_REG_OFFSET, HMAC_INTR_STATE_HMAC_DONE_BIT);

    // Copy the digest
    ((uint32_t*)(dst->data))[0] = mmio_region_read32(hmac, HMAC_DIGEST_0_REG_OFFSET);
    ((uint32_t*)(dst->data))[1] = mmio_region_read32(hmac, HMAC_DIGEST_1_REG_OFFSET);
    ((uint32_t*)(dst->data))[2] = mmio_region_read32(hmac, HMAC_DIGEST_2_REG_OFFSET);
    ((uint32_t*)(dst->data))[3] = mmio_region_read32(hmac, HMAC_DIGEST_3_REG_OFFSET);
    ((uint32_t*)(dst->data))[4] = mmio_region_read32(hmac, HMAC_DIGEST_4_REG_OFFSET);
    ((uint32_t*)(dst->data))[5] = mmio_region_read32(hmac, HMAC_DIGEST_5_REG_OFFSET);
    ((uint32_t*)(dst->data))[6] = mmio_region_read32(hmac, HMAC_DIGEST_6_REG_OFFSET);
    ((uint32_t*)(dst->data))[7] = mmio_region_read32(hmac, HMAC_DIGEST_7_REG_OFFSET);

    // Disable HMAC IP
    reg = mmio_region_read32(hmac, HMAC_CFG_REG_OFFSET);
    reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
    mmio_region_write32(hmac, HMAC_CFG_REG_OFFSET, reg);

    // Print the message digest, if we are in debug mode.
#if TITANSSL_BENCHMARK_DEBUG
	for (int i=0; i<dst->n; i++)
	{
		printf("0x%02x\r\n", dst->data[i]);
        uart_wait_tx_done();
	}
#endif
}

void titanssl_benchmark_aes(
        titanssl_buffer_t *const src,
        titanssl_buffer_t *const dst,
        titanssl_buffer_t *const key,
        titanssl_buffer_t *const iv)
{
    mmio_region_t aes;
    uint32_t reg;
    uint8_t *dp_src;
    uint8_t *dp_dst;

    // Get the AES IP base address
    aes = mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR);

    // Reset the IP
    while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_IDLE_BIT));
    reg = bitfield_bit32_write(0, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);
    reg = bitfield_bit32_write(0, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);
    reg = bitfield_bit32_write(reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);
    mmio_region_write32(aes, AES_TRIGGER_REG_OFFSET, reg);
    while (!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_IDLE_BIT));
    reg = bitfield_field32_write(0, AES_CTRL_SHADOWED_OPERATION_FIELD, AES_CTRL_SHADOWED_OPERATION_MASK);
    reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_MODE_FIELD, AES_CTRL_SHADOWED_MODE_VALUE_AES_NONE);
    reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD, AES_CTRL_SHADOWED_KEY_LEN_MASK);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);

    // Initialize AES IP configurations
    while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_IDLE_BIT));
    reg = bitfield_field32_write(0, AES_CTRL_SHADOWED_OPERATION_FIELD, AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
    reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_MODE_FIELD, AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC);
    reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD, AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256);
    reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_PRNG_RESEED_RATE_FIELD, AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64);
    reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, false);
    reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_SIDELOAD_BIT, false);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);

    // Initialize AES IP auxiliary configurations
    reg = bitfield_bit32_write(0, AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT, false);
    reg = bitfield_bit32_write(reg, AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT, false);
    mmio_region_write32(aes, AES_CTRL_AUX_SHADOWED_REG_OFFSET, reg);
    mmio_region_write32(aes, AES_CTRL_AUX_SHADOWED_REG_OFFSET, reg);
    mmio_region_write32(aes, AES_CTRL_AUX_REGWEN_REG_OFFSET, true);

    // Initialize key shares
    mmio_region_write32(aes, AES_KEY_SHARE0_0_REG_OFFSET, ((uint32_t*)(key->data))[0]);
    mmio_region_write32(aes, AES_KEY_SHARE0_1_REG_OFFSET, ((uint32_t*)(key->data))[1]);
    mmio_region_write32(aes, AES_KEY_SHARE0_2_REG_OFFSET, ((uint32_t*)(key->data))[2]);
    mmio_region_write32(aes, AES_KEY_SHARE0_3_REG_OFFSET, ((uint32_t*)(key->data))[3]);
    mmio_region_write32(aes, AES_KEY_SHARE0_4_REG_OFFSET, ((uint32_t*)(key->data))[4]);
    mmio_region_write32(aes, AES_KEY_SHARE0_5_REG_OFFSET, ((uint32_t*)(key->data))[5]);
    mmio_region_write32(aes, AES_KEY_SHARE0_6_REG_OFFSET, ((uint32_t*)(key->data))[6]);
    mmio_region_write32(aes, AES_KEY_SHARE0_7_REG_OFFSET, ((uint32_t*)(key->data))[7]);
    mmio_region_write32(aes, AES_KEY_SHARE1_0_REG_OFFSET, ((uint32_t*)(key->data))[0]);
    mmio_region_write32(aes, AES_KEY_SHARE1_1_REG_OFFSET, ((uint32_t*)(key->data))[1]);
    mmio_region_write32(aes, AES_KEY_SHARE1_2_REG_OFFSET, ((uint32_t*)(key->data))[2]);
    mmio_region_write32(aes, AES_KEY_SHARE1_3_REG_OFFSET, ((uint32_t*)(key->data))[3]);
    mmio_region_write32(aes, AES_KEY_SHARE1_4_REG_OFFSET, ((uint32_t*)(key->data))[4]);
    mmio_region_write32(aes, AES_KEY_SHARE1_5_REG_OFFSET, ((uint32_t*)(key->data))[5]);
    mmio_region_write32(aes, AES_KEY_SHARE1_6_REG_OFFSET, ((uint32_t*)(key->data))[6]);
    mmio_region_write32(aes, AES_KEY_SHARE1_7_REG_OFFSET, ((uint32_t*)(key->data))[7]);

    // Initialize IV
    reg = mmio_region_read32(aes, AES_CTRL_SHADOWED_REG_OFFSET);
    reg = bitfield_field32_read(reg, AES_CTRL_SHADOWED_MODE_FIELD);
    if (reg != AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB)
    {
        while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_IDLE_BIT));
        mmio_region_write32(aes, AES_IV_0_REG_OFFSET, ((uint32_t*)(iv->data))[0]);
        mmio_region_write32(aes, AES_IV_1_REG_OFFSET, ((uint32_t*)(iv->data))[1]);
        mmio_region_write32(aes, AES_IV_2_REG_OFFSET, ((uint32_t*)(iv->data))[2]);
        mmio_region_write32(aes, AES_IV_3_REG_OFFSET, ((uint32_t*)(iv->data))[3]);
    }

    // Compute AES
    dp_src = src->data;
    dp_dst = dst->data;
    mmio_region_write32(aes, AES_DATA_IN_0_REG_OFFSET, ((uint32_t*)dp_src)[0]);
    mmio_region_write32(aes, AES_DATA_IN_1_REG_OFFSET, ((uint32_t*)dp_src)[1]);
    mmio_region_write32(aes, AES_DATA_IN_2_REG_OFFSET, ((uint32_t*)dp_src)[2]);
    mmio_region_write32(aes, AES_DATA_IN_3_REG_OFFSET, ((uint32_t*)dp_src)[3]);
    while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_INPUT_READY_BIT));
    dp_src += 16;
    
    while (dp_src - src->data < src->n) {
        mmio_region_write32(aes, AES_DATA_IN_0_REG_OFFSET, ((uint32_t*)dp_src)[0]);
        mmio_region_write32(aes, AES_DATA_IN_1_REG_OFFSET, ((uint32_t*)dp_src)[1]);
        mmio_region_write32(aes, AES_DATA_IN_2_REG_OFFSET, ((uint32_t*)dp_src)[2]);
        mmio_region_write32(aes, AES_DATA_IN_3_REG_OFFSET, ((uint32_t*)dp_src)[3]);

        while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_OUTPUT_VALID_BIT));
        ((uint32_t*)(dp_dst))[0] = mmio_region_read32(aes, AES_DATA_OUT_0_REG_OFFSET);
        ((uint32_t*)(dp_dst))[1] = mmio_region_read32(aes, AES_DATA_OUT_1_REG_OFFSET);
        ((uint32_t*)(dp_dst))[2] = mmio_region_read32(aes, AES_DATA_OUT_2_REG_OFFSET);
        ((uint32_t*)(dp_dst))[3] = mmio_region_read32(aes, AES_DATA_OUT_3_REG_OFFSET);
        dp_dst += 16;
        dp_src += 16;
    }
    while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_OUTPUT_VALID_BIT));
    ((uint32_t*)(dp_dst))[0] = mmio_region_read32(aes, AES_DATA_OUT_0_REG_OFFSET);
    ((uint32_t*)(dp_dst))[1] = mmio_region_read32(aes, AES_DATA_OUT_1_REG_OFFSET);
    ((uint32_t*)(dp_dst))[2] = mmio_region_read32(aes, AES_DATA_OUT_2_REG_OFFSET);
    ((uint32_t*)(dp_dst))[3] = mmio_region_read32(aes, AES_DATA_OUT_3_REG_OFFSET);

    // Reset operation mode, key, iv, and data registers
    while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_IDLE_BIT));
    reg = bitfield_bit32_write(0, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);
    mmio_region_write32(aes, AES_CTRL_SHADOWED_REG_OFFSET, reg);
    reg = bitfield_bit32_write(0, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);
    reg = bitfield_bit32_write(reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);
    mmio_region_write32(aes, AES_TRIGGER_REG_OFFSET, reg);
    while (!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_IDLE_BIT));

    // Print the message digest, if we are in debug mode.
#if TITANSSL_BENCHMARK_DEBUG
	for (int i=0; i<dst->n; i++)
	{
		printf("0x%02x\r\n", dst->data[i]);
        uart_wait_tx_done();
	}
#endif
}

int main(
        int argc, 
        char **argv)
{
#ifdef TARGET_SYNTHESIS
#define baud_rate 115200
#define test_freq 50000000
#else
#define baud_rate 115200
#define test_freq 100000000
#endif
	uart_set_cfg(
        0,
        (test_freq/baud_rate)>>4
    );

    initialize_edn();
    initialize_memory(
        (uint8_t*)TITANSSL_DATA_SRC,
        TITANSSL_PAYLOAD_SIZE,
        (uint8_t*)TITANSSL_DATA_DST,
        TITANSSL_OUTPUT_SIZE,
        (uint8_t*)TITANSSL_DATA_KEY,
        TITANSSL_KEY_SIZE,
        (uint8_t*)TITANSSL_DATA_IV,
        TITANSSL_IV_SIZE
    );
    titanssl_benchmark(
        &titanssl_data_src,
        &titanssl_data_dst,
        &titanssl_data_key,
        &titanssl_data_iv
    );

	return 0;
}
