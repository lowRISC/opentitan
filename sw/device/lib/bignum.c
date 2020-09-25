// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/bignum.h"

#define MIN(a, b) (a < b ? a : b)
#define MAX(a, b) (a < b ? b : a)

static uint32_t *bignum_ctx_alloc(bignum_ctx_t *ctx, size_t len) {
  if (ctx->len + len > ctx->cappacity) {
    return NULL;
  }

  uint32_t *ptr = ctx->buffer + ctx->len;
  ctx->len += len;
  return ptr;
}

static void bignum_ctx_free(bignum_ctx_t *ctx) {
  ctx->len = 0;
}

static uint32_t bignum_sub_word(uint32_t w1, uint32_t w2, uint32_t *borrow) {
  w1 -= *borrow;
  if (w2 > w1) {
    *borrow = 1;
    return ~(w2 - w1) + 1;
  } else {
    *borrow = (w1 == ~0 ? 1 : 0);
    return w1 - w2;
  }
}

// Computes r = r + (a * b / 2^32) (mod n). The result may exceed n, but will
// never exceed 2*n. To keep the result within the length of r, this function
// will return `true` if an addtional carry bit results. The caller should
// perform r = r - n in this case to prevent overflow.
static bool bignum_mont_mul_add(uint32_t *r, const uint32_t *a, uint32_t b,
                                const uint32_t *n, uint32_t n_inv, size_t len) {
  // Compute the following:
  //   u = ((r[0] + a[0] * b) * -n_inv) mod 2^32
  //   r = (r + a * b + u * n) / 2^32
  uint64_t work = r[0] + (uint64_t)a[0] * b;
  uint32_t u = (uint32_t)work * -n_inv;

  // Two carries are needed since we are doing 32-bit * 32-bit + 32-bit * 32-bit
  // operations.
  uint32_t carry_a = work >> 32;
  work = (uint32_t)work + (uint64_t)n[0] * u;
  uint32_t carry_b = work >> 32;

  for (int i = 1; i < len; ++i) {
    work = r[i] + (uint64_t)a[i] * b + carry_a;
    carry_a = work >> 32;
    work = (uint32_t)work + (uint64_t)n[i] * u + carry_b;
    carry_b = work >> 32;
    r[i - 1] = work;
  }
  work = (uint64_t)carry_a + carry_b;
  r[len - 1] = work;
  return work > UINT32_MAX;
}

bignum_result_t bignum_init(bignum_t *bn, uint32_t *words, size_t len) {
  if (bn == NULL || words == NULL) {
    return kBignumBadArgs;
  }
  bn->words = words;
  bn->len = len;

  return kBignumOk;
}

bignum_result_t bignum_sub(bignum_t *r, const bignum_t *a, const bignum_t *b) {
  if (a->len > r->len) {
    return kBignumOutOfBounds;
  }

  // Ensure `b` after the shift doesn't contain more words than `a`.
  if (b->len > a->len) {
    return kBignumUnderflow;
  }

  // Perform the subtraction.
  int borrow = 0;
  int i;
  for (i = 0; i < a->len; ++i) {
    uint32_t w1, w2;
    w1 = a->words[i] - borrow;
    w2 = b->words[i];
    if (w2 > w1) {
      r->words[i] = ~(w2 - w1) + 1;
      borrow = 1;
    } else {
      r->words[i] = w1 - w2;
      borrow = 0;
    }
  }
  for (i = a->len - 1; i >= 0 && r->words[i] == 0; --i);
  r->len = i + 1;

  if (borrow != 0) {
    return kBignumUnderflow;
  }

  return kBignumOk;
}

bignum_cmp_result_t bignum_cmp(const bignum_t *a, const bignum_t *b) {
  for (int i = a->len - 1; i > b->len - 1; --i) {
    if (a->words[i] != 0u) {
      return kBignumCmpGt;
    }
  }

  for (int i = b->len - 1; i > a->len - 1; --i) {
    if (b->words[i] != 0u) {
      return kBignumCmpLt;
    }
  }

  for (int i = MIN(a->len, b->len) - 1; i >= 0; --i) {
    uint32_t w1, w2;
    w1 = a->words[i];
    w2 = b->words[i];
    if (w1 > w2) {
      return kBignumCmpGt;
    }
    if (w1 < w2) {
      return kBignumCmpLt;
    }
  }

  return kBignumCmpEq;
}

bignum_result_t bignum_to_montgomery(bignum_t *r, const bignum_t *a,
    const bignum_t *n) {
  // r = a
  if (r != a) {
    memcpy(r->words, a->words, a->len * sizeof(uint32_t));
    r->len = a->len;
  }

  // Since R == 2^(bit-length of n) we can compute aR mod n by repeated bit
  // shifts and subtraction by n.
  for (int i = 0; i < n->len * 32; ++i) {
    // r = r << 1 with msb carry
    uint32_t carry = 0;
    for (int j = 0; j < r->len; ++j) {
      uint32_t new_word = (r->words[j] << 1) | carry;
      carry = r->words[j] >> 31;
      r->words[j] = new_word;
    }

    // carry != 0 implies r > n
    // r < 2*n && r > n implies r - n == r mod n
    if (carry != 0 || bignum_cmp(r, n) != kBignumCmpLt) {
      // r = r - n
      uint32_t borrow = 0;
      for (int j = 0; j < r->len; ++j) {
        r->words[j] = bignum_sub_word(r->words[j], n->words[j], &borrow);
      }

      // Check the carry bit aginst the borrow bit. carry == 1 && borrow == 0
      // implies that r > n, and borrow == 1 && carry == 0 implies that an
      // underflow has taken place (r < 0). Both of these conditions should
      // never occur.
      if (borrow != carry) {
        return kBignumError;
      }
    }
  }

  return kBignumOk;
}

uint32_t bignum_mont_mod_inverse(uint32_t a) {
  // a^-1 = a (mod 2^3).
  uint32_t a_inv = a;
  // Construct the inverse of the next power of 2 through a recurance relation.
  for (int i = 4; i <= 32; ++i) {
    // Find a^-1 mod 2^i.
    a_inv = a_inv * (2 - a * a_inv);
  }
  return a_inv;
}

bignum_result_t bignum_mul_montgomery(bignum_t *r, const bignum_t *aR,
    const bignum_t *bR, const bignum_t *n, uint32_t n_inv) {
  size_t len = n->len;
  if (aR->len < len || bR->len < len || r->len < len) {
    return kBignumBadArgs;
  }
  memset(r->words, 0, r->len * sizeof(uint32_t));

  for (int i = 0; i < len; ++i) {
    if (bignum_mont_mul_add(r->words, aR->words, bR->words[i], n->words, n_inv,
                        len)) {
      bignum_result_t res = bignum_sub(r, r, n);
      // Underflowing should be expected here since r is missing the carry bit.
      if (res == kBignumOk) {
        return kBignumError;
      }
      if (res != kBignumUnderflow) {
        return res;
      }
    }
  }

  if (bignum_cmp(r, n) != kBignumCmpLt) {
    return bignum_sub(r, r, n);
  }

  return kBignumOk;
}

bignum_result_t bignum_mod_exp_by_word(bignum_t *r, const bignum_t *a,
    uint32_t e, const bignum_t *n, bignum_ctx_t *ctx) {
  if (n->len == 0) {
    return kBignumBadArgs;
  }

  // r = 1
  memset(r->words, 0, r->len * sizeof(uint32_t));
  r->words[0] = 1u;
  if (e == 0) {
    return kBignumOk;
  }

  uint32_t *tmp_buf = bignum_ctx_alloc(ctx, n->len);
  if (tmp_buf == NULL) {
    return kBignumOutOfMemory;
  }
  bignum_t tmp1 = {
    .words = tmp_buf,
    .len = n->len,
  };

  tmp_buf = bignum_ctx_alloc(ctx, n->len);
  if (tmp_buf == NULL) {
    bignum_ctx_free(ctx);
    return kBignumOutOfMemory;
  }
  bignum_t tmp2 = {
    .words = tmp_buf,
    .len = n->len,
  };

  // tmp1 = aR mod n
  bignum_result_t res = bignum_to_montgomery(&tmp1, a, n);
  if (res != kBignumOk) {
    goto cleanup;
  }
  
  // r = rR mod n = R mod n
  res = bignum_to_montgomery(r, r, n);
  if (res != kBignumOk) {
    goto cleanup;
  }

  uint32_t n_inv = bignum_mont_mod_inverse(n->words[0]);
  while (e != 0) {
    if ((e & 1u) != 0) {
      // tmp2 = r * tmp1 * R^-1 mod n
      res = bignum_mul_montgomery(&tmp2, r, &tmp1, n, n_inv);
      if (res != kBignumOk) {
        goto cleanup;
      }
      // r = tmp2
      memcpy(r->words, tmp2.words, r->len * sizeof(uint32_t));
    }

    res = bignum_mul_montgomery(&tmp2, &tmp1, &tmp1, n, n_inv);
    if (res != kBignumOk) {
      goto cleanup;
    }
    memcpy(tmp1.words, tmp2.words, tmp1.len * sizeof(uint32_t));
    e >>= 1;
  }

  // Convert result back from montgomery form.
  memset(tmp1.words, 0, tmp1.len * sizeof(uint32_t));
  tmp1.words[0] = 1u;
  res = bignum_mul_montgomery(&tmp2, r, &tmp1, n, n_inv);
  if (res != kBignumOk) {
    goto cleanup;
  }
  memcpy(r->words, tmp2.words, r->len * sizeof(uint32_t));

cleanup:
  bignum_ctx_free(ctx);
  return res;
}
