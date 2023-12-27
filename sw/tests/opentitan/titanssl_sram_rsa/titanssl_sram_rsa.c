// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/runtime/ibex.h"

#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/silicon_creator/rom/string_lib.h"
#include "sw/device/lib/dif/dif_uart.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#include "otbn_regs.h"

#define TARGET_SYNTHESIS


typedef struct
{
    uint8_t  *data;
    uint32_t n;
} titanssl_buffer_t;


static titanssl_buffer_t buffer_plain;
static titanssl_buffer_t buffer_cipher;
static titanssl_buffer_t buffer_modulus;
static titanssl_buffer_t buffer_private;

OTBN_DECLARE_APP_SYMBOLS(rsa);
OTBN_DECLARE_SYMBOL_ADDR(rsa, mode);
OTBN_DECLARE_SYMBOL_ADDR(rsa, n_limbs);
OTBN_DECLARE_SYMBOL_ADDR(rsa, inout);
OTBN_DECLARE_SYMBOL_ADDR(rsa, modulus);
OTBN_DECLARE_SYMBOL_ADDR(rsa, exp);

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(rsa);
static const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(rsa, mode);
static const otbn_addr_t kOtbnVarRsaNLimbs = OTBN_ADDR_T_INIT(rsa, n_limbs);
static const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(rsa, inout);
static const otbn_addr_t kOtbnVarRsaModulus = OTBN_ADDR_T_INIT(rsa, modulus);
static const otbn_addr_t kOtbnVarRsaExp = OTBN_ADDR_T_INIT(rsa, exp);


/* ============================================================================
 * Benchmark setup
 * ========================================================================= */

#define TITANSSL_CFG_DEBUG    1
#define TITANSSL_CFG_MEM_L3   1
#define TITANSSL_CFG_MEM_L1   0
#define TITANSSL_CFG_KEY_512  1
#define TITANSSL_CFG_KEY_1024 0

/* ============================================================================
 * Benchmark automatic configuration
 * ========================================================================= */

#if TITANSSL_CFG_MEM_L3
#define TITANSSL_ADDR_PLAIN   0x80710000
#define TITANSSL_ADDR_CIPHER  0x80720000
#define TITANSSL_ADDR_MODULUS 0xe0004000
#define TITANSSL_ADDR_PRIVATE 0xe0005000
#elif TITANSSL_CFG_MEM_L1
#define TITANSSL_ADDR_PLAIN   0xe0002000
#define TITANSSL_ADDR_CIPHER  0xe0003000
#define TITANSSL_ADDR_MODULUS 0xe0004000
#define TITANSSL_ADDR_PRIVATE 0xe0005000
#else
#error "Wrong benchmark memory configuration"
#endif

#if TITANSSL_CFG_KEY_512

#define TITANSSL_SIZE_KEY 64
static const uint8_t TITANSSL_TEST_PLAIN[TITANSSL_SIZE_KEY] = {
    "Hello OTBN, can you encrypt and decrypt this for me?"
};
static const uint8_t TITANSSL_TEST_MODULUS[TITANSSL_SIZE_KEY] = {
    0xf3, 0xb7, 0x91, 0xce, 0x6e, 0xc0, 0x57, 0xcd, 0x19, 0x63, 0xb9,
    0x6b, 0x81, 0x97, 0x96, 0x40, 0x81, 0xd8, 0x89, 0x27, 0xec, 0x0a,
    0xb1, 0xf2, 0x4a, 0xda, 0x2e, 0x68, 0xe1, 0x80, 0xa4, 0x4f, 0xe0,
    0x82, 0x87, 0x1f, 0x98, 0xdc, 0x42, 0xc7, 0xc2, 0xce, 0xa2, 0xb2,
    0x1a, 0x3f, 0x77, 0xdc, 0xc6, 0x27, 0x6d, 0x83, 0x5c, 0xcd, 0x1d,
    0xdf, 0xe5, 0xf3, 0x98, 0xe6, 0x8b, 0xe6, 0x5b, 0xd4
};
static const uint8_t TITANSSL_TEST_PRIVATE[TITANSSL_SIZE_KEY] = {
    0xc1, 0xf3, 0x5d, 0x18, 0x12, 0x7e, 0xe7, 0x0c, 0xbf, 0x33, 0xd0,
    0x1c, 0xd8, 0x5d, 0x91, 0x26, 0xb6, 0xc5, 0xae, 0x78, 0xda, 0x4c,
    0xae, 0x43, 0xa1, 0x57, 0xab, 0x32, 0xcf, 0xa4, 0xd4, 0x72, 0x20,
    0x53, 0x30, 0x55, 0x7a, 0x93, 0xd9, 0xae, 0x75, 0x32, 0x9d, 0x09,
    0x18, 0x06, 0xc8, 0x26, 0x64, 0x28, 0xcf, 0x2c, 0x3b, 0x6e, 0x6b,
    0x5c, 0x28, 0xde, 0x76, 0x6c, 0x2f, 0xcc, 0xf3, 0x31
};
static const uint8_t TITANSSL_TEST_OUTPUT[TITANSSL_SIZE_KEY] = {
    0xb7, 0x02, 0x28, 0xcb, 0x63, 0x5e, 0xa6, 0xfd, 0x55, 0x4a, 0x85,
    0x43, 0x1d, 0x26, 0x13, 0xb3, 0x78, 0x66, 0xd9, 0xe2, 0xe1, 0xbf,
    0x29, 0xc6, 0xc6, 0xdd, 0x90, 0x76, 0x3f, 0x1d, 0x43, 0xc0, 0x76,
    0x51, 0x75, 0x10, 0x66, 0x61, 0x8c, 0x3c, 0x99, 0xd9, 0x90, 0xd2,
    0x59, 0x45, 0x0a, 0x7a, 0x6d, 0x58, 0xaa, 0x75, 0xf2, 0x63, 0xb3,
    0xe1, 0x06, 0x4b, 0x82, 0x0a, 0xdd, 0x07, 0x44, 0x2a
};

#elif TITANSSL_CFG_KEY_1024

#define TITANSSL_SIZE_KEY 128
static const uint8_t TITANSSL_TEST_PLAIN[TITANSSL_SIZE_KEY] = {
    "Hello OTBN, can you encrypt and decrypt this for me?"
};
static const uint8_t TITANSSL_TEST_MODULUS[TITANSSL_SIZE_KEY] = {
    0x69, 0xef, 0x70, 0x5d, 0xcd, 0xf5, 0x15, 0xb5, 0x6b, 0xa2, 0xcd, 0x2b,
    0x76, 0x3c, 0x6e, 0xdc, 0x13, 0x7,  0x6a, 0x9,  0x80, 0xe2, 0x2a, 0x24,
    0xc2, 0xb0, 0x32, 0x36, 0x67, 0x1b, 0x1d, 0xf2, 0xaa, 0xf9, 0xd4, 0xeb,
    0xc6, 0xf0, 0x3c, 0xe5, 0x94, 0x85, 0xd9, 0xc8, 0xa4, 0x79, 0x35, 0x77,
    0x38, 0x10, 0x1,  0x74, 0xc3, 0xd7, 0x6b, 0x10, 0xc2, 0xc1, 0x5d, 0xa0,
    0x57, 0x11, 0xd8, 0xc7, 0xd9, 0xdf, 0x78, 0xc5, 0xc3, 0x9,  0x84, 0x4d,
    0x28, 0x6c, 0xea, 0x55, 0x87, 0x35, 0x44, 0x85, 0xde, 0x70, 0xa8, 0xec,
    0x60, 0x3b, 0x7c, 0x5,  0x12, 0xb5, 0xb3, 0xbd, 0x75, 0x4,  0x40, 0x2b,
    0x6a, 0x35, 0x4,  0x21, 0x73, 0x5,  0x94, 0x8,  0x8,  0x2c, 0xe9, 0xb4,
    0x8c, 0xd,  0x7c, 0x76, 0xc5, 0x85, 0xa7, 0xa,  0xa1, 0x91, 0xe0, 0xad,
    0xae, 0xfa, 0xb,  0xc5, 0xc4, 0x88, 0x7e, 0xbe
};
static const uint8_t TITANSSL_TEST_PRIVATE[TITANSSL_SIZE_KEY] = {
    0x1,  0x66, 0x7f, 0x2,  0xdb, 0x27, 0x92, 0x7d, 0xd6, 0x41, 0x4e, 0xbf,
    0x47, 0x31, 0x95, 0x8e, 0xfb, 0x5d, 0xee, 0xa1, 0xdf, 0x6d, 0x31, 0xd2,
    0xeb, 0xee, 0xe2, 0xf4, 0xa4, 0x21, 0xa9, 0xb9, 0xd2, 0xcf, 0x94, 0xfe,
    0x13, 0x74, 0xc8, 0xc8, 0xc1, 0x38, 0x6f, 0xb0, 0x84, 0x9c, 0x57, 0x1,
    0x58, 0x91, 0xd6, 0x4,  0x4b, 0x9d, 0x49, 0x3,  0x6,  0x2e, 0x5c, 0xb1,
    0xe2, 0xb7, 0x66, 0x0,  0xf7, 0xad, 0xbb, 0xce, 0xc,  0x46, 0xa5, 0xeb,
    0xd9, 0x32, 0xc2, 0xf8, 0xca, 0xe7, 0xf1, 0xae, 0x8,  0x77, 0xce, 0xc4,
    0xa0, 0xa0, 0xdc, 0xef, 0x6d, 0x4c, 0xd7, 0xf0, 0x7a, 0x66, 0xf3, 0x2f,
    0xd5, 0x54, 0xde, 0xa8, 0xe5, 0xfb, 0xa9, 0xa2, 0x36, 0x21, 0xae, 0xff,
    0xd,  0xfa, 0xba, 0x6b, 0xfd, 0xa3, 0x6a, 0x84, 0xa4, 0x8b, 0x95, 0xd6,
    0xac, 0x5d, 0x4e, 0x2e, 0x7b, 0x14, 0x1f, 0x3d
};
static const uint8_t TITANSSL_TEST_OUTPUT[TITANSSL_SIZE_KEY] = {
    0x76, 0x71, 0x99, 0x16, 0x38, 0x3a, 0xe0, 0xca, 0x9e, 0xc4, 0x5e, 0x9b,
    0x68, 0xb6, 0x3f, 0x78, 0x0d, 0x6e, 0x43, 0x7c, 0xaf, 0x24, 0xcc, 0x3e,
    0x4a, 0xd0, 0x3c, 0x15, 0xc6, 0x10, 0xf8, 0x3a, 0x1a, 0x6e, 0xe8, 0x8f,
    0x9e, 0x6b, 0xdb, 0x3d, 0xd3, 0x48, 0x51, 0x20, 0x8a, 0xb9, 0x36, 0xfb,
    0x9c, 0x2a, 0xd9, 0xef, 0xfc, 0x24, 0x7f, 0xb7, 0x81, 0x7d, 0x81, 0xb2,
    0x6f, 0xd0, 0x1e, 0xdd, 0x5c, 0x70, 0x1b, 0x79, 0x3b, 0x67, 0xe5, 0xfa,
    0xaf, 0x2e, 0xf3, 0xb2, 0xc6, 0xb1, 0xb9, 0x6d, 0x18, 0x79, 0x1a, 0xed,
    0x29, 0xfd, 0xf5, 0x27, 0x8c, 0xf2, 0x6e, 0xe4, 0x48, 0x88, 0xaf, 0x75,
    0xf5, 0xed, 0x09, 0xe7, 0x92, 0xbb, 0x30, 0x97, 0x1e, 0x45, 0x68, 0x81,
    0x6d, 0x69, 0x75, 0xcb, 0xbb, 0xbc, 0xc2, 0x51, 0x6e, 0xb8, 0xc9, 0x46,
    0x57, 0xe5, 0x27, 0xf7, 0x21, 0xb8, 0xd7, 0x2f
};

#else
#error "Wrong benchmark key configuration"
#endif

/* ============================================================================
 * Benchmark implementation
 * ========================================================================= */

void initialize_memory()
{
    buffer_plain.data = (uint8_t*)TITANSSL_ADDR_PLAIN;
    buffer_plain.n = TITANSSL_SIZE_KEY;
    for (size_t i=0; i<TITANSSL_SIZE_KEY; i++) buffer_plain.data[i] = TITANSSL_TEST_PLAIN[i];

    buffer_cipher.data = (uint8_t*)TITANSSL_ADDR_CIPHER;
    buffer_cipher.n = TITANSSL_SIZE_KEY;
    for (size_t i=0; i<TITANSSL_SIZE_KEY; i++) buffer_cipher.data[i] = 0x0;

    buffer_modulus.data = (uint8_t*)TITANSSL_ADDR_MODULUS;
    buffer_modulus.n = TITANSSL_SIZE_KEY;
    for (size_t i=0; i<TITANSSL_SIZE_KEY; i++) buffer_modulus.data[i] = TITANSSL_TEST_MODULUS[i];

    buffer_private.data = (uint8_t*)TITANSSL_ADDR_PRIVATE;
    buffer_private.n = TITANSSL_SIZE_KEY;
    for (size_t i=0; i<TITANSSL_SIZE_KEY; i++) buffer_private.data[i] = TITANSSL_TEST_PRIVATE[i];
}

void titanssl_benchmark_rsa_enc(
        titanssl_buffer_t *const plain,
        titanssl_buffer_t *const cipher,
        titanssl_buffer_t *const modulus)
{
    mmio_region_t otbn;
    uint32_t mode;
    uint32_t n_limbs;
    uint32_t reg;

    // Get OTBN base address
    otbn = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);

    // Load OTBN application
    mmio_region_memcpy_to_mmio32(otbn, OTBN_IMEM_REG_OFFSET, kOtbnAppRsa.imem_start, kOtbnAppRsa.imem_end - kOtbnAppRsa.imem_start);
    mmio_region_memcpy_to_mmio32(otbn, OTBN_DMEM_REG_OFFSET, kOtbnAppRsa.dmem_data_start, kOtbnAppRsa.dmem_data_end - kOtbnAppRsa.dmem_data_start);

    // Write input arguments to OTBN
    n_limbs = TITANSSL_SIZE_KEY / 32;
    mode = 1;
    mmio_region_memcpy_to_mmio32(otbn, OTBN_DMEM_REG_OFFSET+kOtbnVarRsaMode, &mode, sizeof(uint32_t));
    mmio_region_memcpy_to_mmio32(otbn, OTBN_DMEM_REG_OFFSET+kOtbnVarRsaNLimbs, &n_limbs, sizeof(uint32_t));
    mmio_region_memcpy_to_mmio32(otbn, OTBN_DMEM_REG_OFFSET+kOtbnVarRsaModulus, modulus->data, TITANSSL_SIZE_KEY);
    mmio_region_memcpy_to_mmio32(otbn, OTBN_DMEM_REG_OFFSET+kOtbnVarRsaInOut, plain->data, TITANSSL_SIZE_KEY);

    // Call OTBN to perform operation, and wait for it to complete
    mmio_region_write32(otbn, OTBN_CMD_REG_OFFSET, kDifOtbnCmdExecute);
    do
    {
        reg = mmio_region_read32(otbn, OTBN_STATUS_REG_OFFSET);
    } while(bitfield_field32_read(reg, OTBN_STATUS_STATUS_FIELD));
    if (mmio_region_read32(otbn, OTBN_ERR_BITS_REG_OFFSET)) while (true) asm volatile ("wfi");

    // Read back results.
    mmio_region_memcpy_from_mmio32(otbn, OTBN_DMEM_REG_OFFSET+kOtbnVarRsaInOut, cipher->data, TITANSSL_SIZE_KEY);
}

void titanssl_benchmark_rsa_dec(
        titanssl_buffer_t *const plain,
        titanssl_buffer_t *const cipher,
        titanssl_buffer_t *const modulus,
        titanssl_buffer_t *const private)
{
    otbn_t otbn_ctx;
    uint32_t n_limbs;
    uint32_t mode;

    // Get OTBN base address
    otbn_ctx.app_is_loaded = false;
    otbn_ctx.dif.base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);

    // Load OTBN application
    otbn_load_app(&otbn_ctx, kOtbnAppRsa);

    // Write input arguments to OTBN
    n_limbs = TITANSSL_SIZE_KEY / 32;
    mode = 2;
    otbn_copy_data_to_otbn(&otbn_ctx, sizeof(uint32_t), &mode, kOtbnVarRsaMode);
    otbn_copy_data_to_otbn(&otbn_ctx, sizeof(uint32_t), &n_limbs, kOtbnVarRsaNLimbs);
    otbn_copy_data_to_otbn(&otbn_ctx, TITANSSL_SIZE_KEY, modulus->data, kOtbnVarRsaModulus);
    otbn_copy_data_to_otbn(&otbn_ctx, TITANSSL_SIZE_KEY, private->data, kOtbnVarRsaExp);
    otbn_copy_data_to_otbn(&otbn_ctx, TITANSSL_SIZE_KEY, plain->data, kOtbnVarRsaInOut);

    // Call OTBN to perform operation
    otbn_execute(&otbn_ctx);
    otbn_busy_wait_for_done(&otbn_ctx);

    // Read back results.
    otbn_copy_data_from_otbn(&otbn_ctx, TITANSSL_SIZE_KEY, kOtbnVarRsaInOut, cipher->data);
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

    entropy_testutils_auto_mode_init();
    initialize_memory();
    titanssl_benchmark_rsa_enc(
        &buffer_plain,
        &buffer_cipher,
        &buffer_modulus
    );
#if TITANSSL_CFG_DEBUG
    printf("RSA Encryption\r\n");
    for (int i = 0; i < TITANSSL_SIZE_KEY; i++) {
        printf("%02x vs. %02x\r\n", buffer_cipher.data[i], TITANSSL_TEST_OUTPUT[i]);
    }
#endif
    titanssl_benchmark_rsa_dec(
        &buffer_cipher,
        &buffer_plain,
        &buffer_modulus,
        &buffer_private
    );
#if TITANSSL_CFG_DEBUG
    printf("RSA Decryption\r\n");
    for (int i = 0; i < TITANSSL_SIZE_KEY; i++) {
        printf("%02x vs. %02x\r\n", buffer_plain.data[i], TITANSSL_TEST_PLAIN[i]);
    }
#endif

    return 0;
}
