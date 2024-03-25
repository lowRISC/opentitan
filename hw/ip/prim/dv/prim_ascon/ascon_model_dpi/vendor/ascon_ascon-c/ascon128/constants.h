#ifndef CONSTANTS_H_
#define CONSTANTS_H_

#include <stdint.h>

#define ASCON_128_KEYBYTES 16
#define ASCON_128A_KEYBYTES 16
#define ASCON_80PQ_KEYBYTES 20

#define ASCON_128_RATE 8
#define ASCON_128A_RATE 16
#define ASCON_HASH_RATE 8
#define ASCON_PRF_IN_RATE 32
#define ASCON_PRFA_IN_RATE 40
#define ASCON_PRF_OUT_RATE 16

#define ASCON_128_PA_ROUNDS 12
#define ASCON_128_PB_ROUNDS 6
#define ASCON_128A_PA_ROUNDS 12
#define ASCON_128A_PB_ROUNDS 8

#define ASCON_HASH_PA_ROUNDS 12
#define ASCON_HASH_PB_ROUNDS 12
#define ASCON_HASHA_PA_ROUNDS 12
#define ASCON_HASHA_PB_ROUNDS 8

#define ASCON_PRF_PA_ROUNDS 12
#define ASCON_PRF_PB_ROUNDS 12
#define ASCON_PRFA_PA_ROUNDS 12
#define ASCON_PRFA_PB_ROUNDS 8

#define ASCON_128_IV                            \
  (((uint64_t)(ASCON_128_KEYBYTES * 8) << 56) | \
   ((uint64_t)(ASCON_128_RATE * 8) << 48) |     \
   ((uint64_t)(ASCON_128_PA_ROUNDS) << 40) |    \
   ((uint64_t)(ASCON_128_PB_ROUNDS) << 32))

#define ASCON_128A_IV                            \
  (((uint64_t)(ASCON_128A_KEYBYTES * 8) << 56) | \
   ((uint64_t)(ASCON_128A_RATE * 8) << 48) |     \
   ((uint64_t)(ASCON_128A_PA_ROUNDS) << 40) |    \
   ((uint64_t)(ASCON_128A_PB_ROUNDS) << 32))

#define ASCON_80PQ_IV                            \
  (((uint64_t)(ASCON_80PQ_KEYBYTES * 8) << 56) | \
   ((uint64_t)(ASCON_128_RATE * 8) << 48) |      \
   ((uint64_t)(ASCON_128_PA_ROUNDS) << 40) |     \
   ((uint64_t)(ASCON_128_PB_ROUNDS) << 32))

#define ASCON_HASH_IV                                                \
  (((uint64_t)(ASCON_HASH_RATE * 8) << 48) |                         \
   ((uint64_t)(ASCON_HASH_PA_ROUNDS) << 40) |                        \
   ((uint64_t)(ASCON_HASH_PA_ROUNDS - ASCON_HASH_PB_ROUNDS) << 32) | \
   ((uint64_t)(ASCON_HASH_BYTES * 8) << 0))

#define ASCON_HASHA_IV                                                 \
  (((uint64_t)(ASCON_HASH_RATE * 8) << 48) |                           \
   ((uint64_t)(ASCON_HASHA_PA_ROUNDS) << 40) |                         \
   ((uint64_t)(ASCON_HASHA_PA_ROUNDS - ASCON_HASHA_PB_ROUNDS) << 32) | \
   ((uint64_t)(ASCON_HASH_BYTES * 8) << 0))

#define ASCON_XOF_IV                          \
  (((uint64_t)(ASCON_HASH_RATE * 8) << 48) |  \
   ((uint64_t)(ASCON_HASH_PA_ROUNDS) << 40) | \
   ((uint64_t)(ASCON_HASH_PA_ROUNDS - ASCON_HASH_PB_ROUNDS) << 32))

#define ASCON_XOFA_IV                          \
  (((uint64_t)(ASCON_HASH_RATE * 8) << 48) |   \
   ((uint64_t)(ASCON_HASHA_PA_ROUNDS) << 40) | \
   ((uint64_t)(ASCON_HASHA_PA_ROUNDS - ASCON_HASHA_PB_ROUNDS) << 32))

#define ASCON_MAC_IV                                               \
  (((uint64_t)(CRYPTO_KEYBYTES * 8) << 56) |                       \
   ((uint64_t)(ASCON_PRF_OUT_RATE * 8) << 48) |                    \
   ((uint64_t)(0x80 | ASCON_PRF_PA_ROUNDS) << 40) |                \
   ((uint64_t)(ASCON_PRF_PA_ROUNDS - ASCON_PRF_PB_ROUNDS) << 32) | \
   ((uint64_t)(ASCON_PRF_BYTES * 8) << 0))

#define ASCON_MACA_IV                                                \
  (((uint64_t)(CRYPTO_KEYBYTES * 8) << 56) |                         \
   ((uint64_t)(ASCON_PRF_OUT_RATE * 8) << 48) |                      \
   ((uint64_t)(0x80 | ASCON_PRFA_PA_ROUNDS) << 40) |                 \
   ((uint64_t)(ASCON_PRFA_PA_ROUNDS - ASCON_PRFA_PB_ROUNDS) << 32) | \
   ((uint64_t)(ASCON_PRF_BYTES * 8) << 0))

#define ASCON_PRF_IV                                \
  (((uint64_t)(CRYPTO_KEYBYTES * 8) << 56) |        \
   ((uint64_t)(ASCON_PRF_OUT_RATE * 8) << 48) |     \
   ((uint64_t)(0x80 | ASCON_PRF_PA_ROUNDS) << 40) | \
   ((uint64_t)(ASCON_PRF_PA_ROUNDS - ASCON_PRF_PB_ROUNDS) << 32))

#define ASCON_PRFA_IV                                \
  (((uint64_t)(CRYPTO_KEYBYTES * 8) << 56) |         \
   ((uint64_t)(ASCON_PRF_OUT_RATE * 8) << 48) |      \
   ((uint64_t)(0x80 | ASCON_PRFA_PA_ROUNDS) << 40) | \
   ((uint64_t)(ASCON_PRFA_PA_ROUNDS - ASCON_PRFA_PB_ROUNDS) << 32))

#define ASCON_PRFS_IV                               \
  (((uint64_t)(CRYPTO_KEYBYTES * 8) << 56) |        \
   ((uint64_t)(0x40 | ASCON_PRF_PA_ROUNDS) << 40) | \
   ((uint64_t)(ASCON_PRF_BYTES * 8) << 32))

#endif /* CONSTANTS_H_ */
