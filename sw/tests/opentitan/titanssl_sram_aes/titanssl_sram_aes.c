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

#include "aes_regs.h"  // Generated.


#define TARGET_SYNTHESIS


typedef struct
{
    uint8_t *data;
    size_t n;
} titanssl_buffer_t;


static titanssl_buffer_t buffer_plain;
static titanssl_buffer_t buffer_cipher;
static titanssl_buffer_t buffer_key;
static titanssl_buffer_t buffer_iv;


/* ============================================================================
 * Benchmark setup
 * ========================================================================= */

#define TITANSSL_CFG_DEBUG   0
#define TITANSSL_CFG_MEM_L3  1
#define TITANSSL_CFG_MEM_L1  0
#define TITANSSL_CFG_PAYLOAD 8192

/* ============================================================================
 * Benchmark automatic configuration
 * ========================================================================= */

#if TITANSSL_CFG_MEM_L3
#define TITANSSL_ADDR_PLAIN  0x80720000
#define TITANSSL_ADDR_CIPHER 0x80740000
#define TITANSSL_ADDR_KEY    0xe0006000
#define TITANSSL_ADDR_IV     0xe0006100
#elif TITANSSL_CFG_MEM_L1
#define TITANSSL_ADDR_PLAIN  0xe0002000
#define TITANSSL_ADDR_CIPHER 0xe0004000
#define TITANSSL_ADDR_KEY    0xe0006000
#define TITANSSL_ADDR_IV     0xe0006100
#else
#error "Wrong benchmark memory configuration"
#endif

#define TITANSSL_SIZE_PLAIN  ((TITANSSL_CFG_PAYLOAD+0xF) & ~0xF)
#define TITANSSL_SIZE_CIPHER TITANSSL_SIZE_PLAIN
#define TITANSSL_SIZE_KEY    32
#define TITANSSL_SIZE_IV     16

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
    buffer_plain.data = (uint8_t*)TITANSSL_ADDR_PLAIN;
    buffer_plain.n = TITANSSL_SIZE_PLAIN;
    for (size_t i=0; i<TITANSSL_SIZE_PLAIN; i++) buffer_plain.data[i] = 0x0;

    buffer_cipher.data = (uint8_t*)TITANSSL_ADDR_CIPHER;
    buffer_cipher.n = TITANSSL_SIZE_CIPHER;
    for (size_t i=0; i<TITANSSL_SIZE_CIPHER; i++) buffer_cipher.data[i] = 0x0;

    buffer_key.data = (uint8_t*)TITANSSL_ADDR_KEY;
    buffer_key.n = TITANSSL_SIZE_KEY;
    for (size_t i=0; i<TITANSSL_SIZE_KEY; i++) buffer_key.data[i] = 0x0;

    buffer_iv.data = (uint8_t*)TITANSSL_ADDR_IV;
    buffer_iv.n = TITANSSL_SIZE_IV;
    for (size_t i=0; i<TITANSSL_SIZE_IV; i++) buffer_iv.data[i] = 0x0;
}

void titanssl_benchmark_aes(
        titanssl_buffer_t *const plain,
        titanssl_buffer_t *const cipher,
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
    dp_src = plain->data;
    dp_dst = cipher->data;
    mmio_region_write32(aes, AES_DATA_IN_0_REG_OFFSET, ((uint32_t*)dp_src)[0]);
    mmio_region_write32(aes, AES_DATA_IN_1_REG_OFFSET, ((uint32_t*)dp_src)[1]);
    mmio_region_write32(aes, AES_DATA_IN_2_REG_OFFSET, ((uint32_t*)dp_src)[2]);
    mmio_region_write32(aes, AES_DATA_IN_3_REG_OFFSET, ((uint32_t*)dp_src)[3]);
    while(!mmio_region_get_bit32(aes, AES_STATUS_REG_OFFSET, AES_STATUS_INPUT_READY_BIT));
    dp_src += 16;
    
    while (dp_src - plain->data < plain->n) {
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
    titanssl_benchmark_aes(
        &buffer_plain,
        &buffer_cipher,
        &buffer_key,
        &buffer_iv
    );

#if TITANSSL_CFG_DEBUG
	for (int i=0; i<buffer_cipher.n; i++)
	{
		printf("0x%02x\r\n", buffer_cipher.data[i]);
        uart_wait_tx_done();
	}
#endif

	return 0;
}
