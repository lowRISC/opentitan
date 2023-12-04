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
    uint8_t  *data;
    uint32_t n;
} titanssl_batch_t;

typedef struct __attribute__((packed))
{
    titanssl_batch_t *src;
    titanssl_batch_t *dst;
    uint32_t         n_src;
    uint32_t         n_dst;
} titanssl_mbox_t;


#define TITANSSL_TEST_SRC_SIZE  1500
#define TITANSSL_TEST_DST_SIZE  32
#define TITANSSL_PAGE_SIZE      4096
#define TITANSSL_MBOX_BASE      0x10404000
#define TITANSSL_BATCH_SRC_BASE 0x80700000
#define TITANSSL_BATCH_DST_BASE 0x80701000
#define TITANSSL_DATA_SRC_BASE  0x80720000
#define TITANSSL_DATA_DST_BASE  0x80740000


#if TITANSSL_TEST_SRC_SIZE == 65536
#pragma message("TITANSSL_TEST_SRC_SIZE is 65536")

static const dif_hmac_digest_t kExpectedShaDigest = {
    .digest =
    {
        0x9ca9cc31, 0x731c23ae, 0x4f489eac, 0x9f3df0de,
        0x7505dc0b, 0x7747c2b9, 0x64a0af79, 0xde2f2560
    },
};

#elif TITANSSL_TEST_SRC_SIZE == 2354
#pragma message("TITANSSL_TEST_SRC_SIZE is 2354")

static const dif_hmac_digest_t kExpectedShaDigest = {
    .digest =
    {
        0x84e631cb, 0x66215bde, 0x0c06983c, 0x55cf25ac,
        0x61b32a43, 0x0644802f, 0xe0df0f84, 0xdbf966ec
    },
};

#elif TITANSSL_TEST_SRC_SIZE == 1500
#pragma message("TITANSSL_TEST_SRC_SIZE is 1500")

static const dif_hmac_digest_t kExpectedShaDigest = {
    .digest =
    {
        0xd856ee73, 0x4f83940f, 0x0a9dd94f, 0x02385d59,
        0x50a3026e, 0x42b8e381, 0x681dd8a5, 0x6249da5c
    },
};

#else
#error "Supported TITANSSL_TEST_SRC_SIZE are 65536, 2354, 1500"
#endif // TITANSSL_TEST_SRC_SIZE


static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};


static titanssl_mbox_t* const titanssl_mbox = (titanssl_mbox_t*)TITANSSL_MBOX_BASE;
static dif_hmac_digest_t *titanssl_digest = 0x0;


void initialize_memory()
{
    uint32_t n = 0;
    uint8_t *p = 0;

    // Initialize mailbox content
    titanssl_mbox->src = (titanssl_batch_t*)TITANSSL_BATCH_SRC_BASE;
    titanssl_mbox->dst = (titanssl_batch_t*)TITANSSL_BATCH_DST_BASE;
    titanssl_mbox->n_src = 1 + (TITANSSL_TEST_SRC_SIZE-1) / TITANSSL_PAGE_SIZE;
    titanssl_mbox->n_dst = 1 + (TITANSSL_TEST_DST_SIZE-1) / TITANSSL_PAGE_SIZE;

    // Initialize batch content
    for (size_t i=0; i<titanssl_mbox->n_src; i++)
    {
        n = TITANSSL_TEST_SRC_SIZE - i*TITANSSL_PAGE_SIZE;
        p = (uint8_t*)(TITANSSL_DATA_SRC_BASE + i*TITANSSL_PAGE_SIZE);

        titanssl_mbox->src[i].data = p;
        if (n > TITANSSL_PAGE_SIZE)
        {
            for (size_t j=0; j<TITANSSL_PAGE_SIZE; j++) p[j] = 0x0;
            titanssl_mbox->src[i].n = TITANSSL_PAGE_SIZE;
        } else {
            for (size_t j=0; j<n; j++) p[j] = 0x0;
            titanssl_mbox->src[i].n = n;
        }
    }
    for (size_t i=0; i<titanssl_mbox->n_dst; i++)
    {
        n = TITANSSL_TEST_DST_SIZE - i*TITANSSL_PAGE_SIZE;
        p = (uint8_t*)(TITANSSL_DATA_DST_BASE + i*TITANSSL_PAGE_SIZE);

        titanssl_mbox->dst[i].data = p;
        if (n > TITANSSL_PAGE_SIZE)
        {
            for (size_t j=0; j<TITANSSL_PAGE_SIZE; j++) p[j] = 0x0;
            titanssl_mbox->dst[i].n = TITANSSL_PAGE_SIZE;
        } else {
            for (size_t j=0; j<n; j++) p[j] = 0x0;
            titanssl_mbox->dst[i].n = n;
        }
    }
}

void titanssl_sha256()
{
	dif_hmac_t hmac;
	dif_result_t res;

    titanssl_batch_t* const src = titanssl_mbox->src;
    titanssl_batch_t* const dst = titanssl_mbox->dst;
    const uint32_t n_src = titanssl_mbox->n_src;
    const uint32_t n_dst = titanssl_mbox->n_dst;

	// Initialize HMAC IP in SHA256 mode
	res = dif_hmac_init(
		mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR),
		&hmac
	);
   	res = dif_hmac_mode_sha256_start(
		&hmac,
		kHmacTransactionConfig
	);

	// Compute SHA256
    for (size_t i=0; i<n_src; i++)
    {
        const uint8_t *kData = src[i].data;
        const uint32_t kDataSize = src[i].n;
        const uint8_t *dp = src[i].data;

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
}

void check_digest()
{
    titanssl_batch_t* const dst = titanssl_mbox->dst;

	for (int i=0; i<8; i++)
	{
		printf(
            "0x%08x vs. 0x%08x\r\n",
            kExpectedShaDigest.digest[i],
            ((uint32_t*)(dst->data))[i]
        );
        uart_wait_tx_done();
	}
}

int main(int argc, char **argv)
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

    initialize_memory();
    titanssl_sha256();
    check_digest();

	return 0;
}
