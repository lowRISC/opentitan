// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/silicon_creator/rom/string_lib.h"

#include "hmac_regs.h"  // Generated.


#define TARGET_SYNTHESIS


typedef struct
{
    uint8_t *data;
    size_t n;
} titanssl_buffer_t;


static titanssl_buffer_t buffer_payload;
static titanssl_buffer_t buffer_digest;
static titanssl_buffer_t buffer_key;


/* ============================================================================
 * Benchmark setup
 * ========================================================================= */

// Configure debug mode.
#define TITANSSL_CFG_DEBUG     1
#define TITANSSL_CFG_MEM_L3    1
#define TITANSSL_CFG_MEM_L1    0
#define TITANSSL_CFG_PAYLOAD   64
#define TITANSSL_CFG_OP_SHA256 1
#define TITANSSL_CFG_OP_HMAC   0

/* ============================================================================
 * Benchmark automatic configuration
 * ========================================================================= */

#if TITANSSL_CFG_MEM_L3
#define TITANSSL_ADDR_PAYLOAD 0x80720000
#define TITANSSL_ADDR_DIGEST  0x80740000
#define TITANSSL_ADDR_KEY     0xe0006000
#elif TITANSSL_BENCHMARK_L1
#define TITANSSL_ADDR_PAYLOAD 0xe0002000
#define TITANSSL_ADDR_DIGEST  0xe0004000
#define TITANSSL_ADDR_KEY     0xe0006000
#else
#error "Wrong benchmark memory configuration"
#endif

#define TITANSSL_SIZE_PAYLOAD TITANSSL_CFG_PAYLOAD
#define TITANSSL_SIZE_DIGEST  32
#define TITANSSL_SIZE_KEY     32

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

void initialize_memory()
{
    buffer_payload.data = (uint8_t*)TITANSSL_ADDR_PAYLOAD;
    buffer_payload.n = TITANSSL_SIZE_PAYLOAD;
    for (size_t i=0; i<TITANSSL_SIZE_PAYLOAD; i++) buffer_payload.data[i] = 0x0;

    buffer_digest.data = (uint8_t*)TITANSSL_ADDR_DIGEST;
    buffer_digest.n = TITANSSL_SIZE_DIGEST;
    for (size_t i=0; i<TITANSSL_SIZE_DIGEST; i++) buffer_digest.data[i] = 0x0;

    buffer_key.data = (uint8_t*)TITANSSL_ADDR_KEY;
    buffer_key.n = TITANSSL_SIZE_KEY;
    for (size_t i=0; i<TITANSSL_SIZE_KEY; i++) buffer_key.data[i] = 0x0;
}

void titanssl_benchmark_hmac(
        titanssl_buffer_t *const payload,
        titanssl_buffer_t *const digest,
        titanssl_buffer_t *const key)
{
    mmio_region_t hmac;
    uint32_t reg;
    const uint8_t *dp;

    // Get the HMAC IP base address
    hmac = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);

    // Initialize HMAC IP with digest and message in little-endian mode
    reg = mmio_region_read32(hmac, HMAC_CFG_REG_OFFSET);
#if TITANSSL_CFG_OP_SHA256
    reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
    reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
    mmio_region_write32(hmac, HMAC_CFG_REG_OFFSET, reg);
#elif TITANSSL_CFG_OP_HMAC
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
    dp = payload->data;
    while (dp < payload->data + payload->n) 
    {
        uint32_t n_bytes;
        uint32_t n_words;

        // Compute how many bytes need will be pushed into the accelerator FIFO.
        n_bytes = 16 * sizeof(uint32_t);
        if (n_bytes > payload->data + payload->n - dp) n_bytes = payload->data + payload->n - dp;
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
    ((uint32_t*)(digest->data))[0] = mmio_region_read32(hmac, HMAC_DIGEST_0_REG_OFFSET);
    ((uint32_t*)(digest->data))[1] = mmio_region_read32(hmac, HMAC_DIGEST_1_REG_OFFSET);
    ((uint32_t*)(digest->data))[2] = mmio_region_read32(hmac, HMAC_DIGEST_2_REG_OFFSET);
    ((uint32_t*)(digest->data))[3] = mmio_region_read32(hmac, HMAC_DIGEST_3_REG_OFFSET);
    ((uint32_t*)(digest->data))[4] = mmio_region_read32(hmac, HMAC_DIGEST_4_REG_OFFSET);
    ((uint32_t*)(digest->data))[5] = mmio_region_read32(hmac, HMAC_DIGEST_5_REG_OFFSET);
    ((uint32_t*)(digest->data))[6] = mmio_region_read32(hmac, HMAC_DIGEST_6_REG_OFFSET);
    ((uint32_t*)(digest->data))[7] = mmio_region_read32(hmac, HMAC_DIGEST_7_REG_OFFSET);

    // Disable HMAC IP
    reg = mmio_region_read32(hmac, HMAC_CFG_REG_OFFSET);
    reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, false);
    reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
    mmio_region_write32(hmac, HMAC_CFG_REG_OFFSET, reg);
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
    initialize_memory();
    titanssl_benchmark_hmac(
        &buffer_payload,
        &buffer_digest,
        &buffer_key
    );

#if TITANSSL_CFG_DEBUG
	for (int i=0; i<buffer_digest.n; i++)
	{
		printf("0x%02x\r\n", buffer_digest.data[i]);
        uart_wait_tx_done();
	}
#endif

	return 0;
}
