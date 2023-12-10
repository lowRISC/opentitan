// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/silicon_creator/rom/string_lib.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"


#define TARGET_SYNTHESIS


typedef struct
{
    uint8_t *data;
    size_t n;
} titanssl_buffer_t;


static titanssl_buffer_t titanssl_data_src;
static titanssl_buffer_t titanssl_data_dst;
static titanssl_buffer_t titanssl_data_key;


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
#define TITANSSL_BENCHMARK_SHA256 1
#define TITANSSL_BENCHMARK_HMAC   0

/* ============================================================================
 * Benchmark automatic configuration
 * ========================================================================= */

#if TITANSSL_BENCHMARK_L3
#define TITANSSL_DATA_SRC 0x80720000
#define TITANSSL_DATA_DST 0x80740000
#define TITANSSL_DATA_KEY 0xe0006000
#elif TITANSSL_BENCHMARK_L1
#define TITANSSL_DATA_SRC 0xe0002000
#define TITANSSL_DATA_DST 0xe0004000
#define TITANSSL_DATA_KEY 0xe0006000
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
#define titanssl_benchmark titanssl_benchmark_sha256
#elif TITANSSL_BENCHMARK_HMAC
#define TITANSSL_OUTPUT_SIZE 32
#define TITANSSL_KEY_SIZE 32
#define titanssl_benchmark titanssl_benchmark_hmac
#else
#error "Wrong benchmark operation configuration"
#endif

/* ============================================================================
 * Benchmark implementation
 * ========================================================================= */

void initialize_memory(
        uint8_t *src_data,
        size_t src_n,
        uint8_t *dst_data,
        size_t dst_n,
        uint8_t *key_data,
        size_t key_n)
{
    titanssl_data_src.data = src_data;
    titanssl_data_src.n = src_n;
    for (size_t i=0; i<src_n; i++)
    {
        titanssl_data_src.data[i] = 0x0;
    }

    titanssl_data_dst.data = dst_data;
    titanssl_data_dst.n = dst_n;
    for (size_t i=0; i<dst_n; i++)
    {
        titanssl_data_dst.data[i] = 0x0;
    }

    titanssl_data_key.data = key_data;
    titanssl_data_key.n = key_n;
    for (size_t i=0; i<key_n; i++)
    {
        titanssl_data_key.data[i] = 0x0;
    }
}

void titanssl_benchmark_sha256(
        titanssl_buffer_t *const src,
        titanssl_buffer_t *const dst,
        titanssl_buffer_t *const key)
{
	dif_hmac_t hmac;
    dif_hmac_transaction_t cfg;
	dif_result_t res;

	// Initialize HMAC IP in SHA256 mode
	res = dif_hmac_init(
		mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR),
		&hmac
	);
    cfg = {
        .digest_endianness = kDifHmacEndiannessLittle,
        .message_endianness = kDifHmacEndiannessLittle,
    };
   	res = dif_hmac_mode_sha256_start(
		&hmac,
		cfg
	);

	// Compute SHA256
    const uint8_t *kData = src->data;
    const uint32_t kDataSize = src->n;
    const uint8_t *dp = src->data;

    while (dp - kData < kDataSize)
    {
        uint32_t sent_bytes;

        res = dif_hmac_fifo_push(
            &hmac,
            dp,
            kDataSize - (dp - kData),
            &sent_bytes
        );
        dp += sent_bytes;

        if (res == kDifIpFifoFull)
        {
            uint32_t fifo_depth;

            do
            {
                res = dif_hmac_fifo_count_entries(
                    &hmac,
                    &fifo_depth
                );
            } while (fifo_depth != 0);
        }
    }
    res = dif_hmac_process(&hmac);
    while (!mmio_region_get_bit32(
        hmac.base_addr,
        HMAC_INTR_STATE_REG_OFFSET,
        HMAC_INTR_STATE_HMAC_DONE_BIT
    ));

    // Finalize SHA256
    do
    {
        res = dif_hmac_finish(
            &hmac,
            (dif_hmac_digest_t*)(dst->data)
        );
    } while(res != kDifOk);

    // Print the message digest, if we are in debug mode.
#if TITANSSL_BENCHMARK_DEBUG
	for (int i=0; i<8; i++)
	{
		printf(
            "0x%08x\r\n",
            ((uint32_t*)(dst->data))[i]
        );
        uart_wait_tx_done();
	}
#endif
}

void titanssl_benchmark_hmac(
        titanssl_buffer_t *const src,
        titanssl_buffer_t *const dst,
        titanssl_buffer_t *const key)
{
	dif_hmac_t hmac;
    dif_hmac_transaction_t cfg;
	dif_result_t res;

	// Initialize HMAC IP in SHA256 mode
	res = dif_hmac_init(
		mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR),
		&hmac
	);
    cfg = {
        .digest_endianness = kDifHmacEndiannessLittle,
        .message_endianness = kDifHmacEndiannessLittle,
    };
   	res = dif_hmac_mode_hmac(
		&hmac,
        key.data,
		kHmacTransactionConfig
	);

	// Compute SHA256
    const uint8_t *kData = src->data;
    const uint32_t kDataSize = src->n;
    const uint8_t *dp = src->data;

    while (dp - kData < kDataSize)
    {
        uint32_t sent_bytes;

        res = dif_hmac_fifo_push(
            &hmac,
            dp,
            kDataSize - (dp - kData),
            &sent_bytes
        );
        dp += sent_bytes;

        if (res == kDifIpFifoFull)
        {
            uint32_t fifo_depth;

            do
            {
                res = dif_hmac_fifo_count_entries(
                    &hmac,
                    &fifo_depth
                );
            } while (fifo_depth != 0);
        }
    }
    res = dif_hmac_process(&hmac);
    while (!mmio_region_get_bit32(
        hmac.base_addr,
        HMAC_INTR_STATE_REG_OFFSET,
        HMAC_INTR_STATE_HMAC_DONE_BIT
    ));

    // Finalize SHA256
    do
    {
        res = dif_hmac_finish(
            &hmac,
            (dif_hmac_digest_t*)(dst->data)
        );
    } while(res != kDifOk);

    // Print the message digest, if we are in debug mode.
#if TITANSSL_BENCHMARK_DEBUG
	for (int i=0; i<8; i++)
	{
		printf(
            "0x%08x\r\n",
            ((uint32_t*)(dst->data))[i]
        );
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

    initialize_memory(
        (uint8_t*)TITANSSL_DATA_SRC,
        TITANSSL_PAYLOAD_SIZE,
        (uint8_t*)TITANSSL_DATA_DST,
        TITANSSL_OUTPUT_SIZE,
        (uint8_t*)TITANSSL_DATA_KEY,
        TITANSSL_KEY_SIZE
    );
    titanssl_benchmark(
        &titanssl_data_src,
        &titanssl_data_dst,
        &titanssl_data_key
    );

	return 0;
}
