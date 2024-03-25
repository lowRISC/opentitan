#include "api.h"
#include "ascon.h"
#include "crypto_aead.h"
#include "permutations.h"
#include "printstate.h"
#include "word.h"

int crypto_aead_encrypt(unsigned char* c, unsigned long long* clen,
                        const unsigned char* m, unsigned long long mlen,
                        const unsigned char* ad, unsigned long long adlen,
                        const unsigned char* nsec, const unsigned char* npub,
                        const unsigned char* k) {
  (void)nsec;

  /* set ciphertext size */
  *clen = mlen + CRYPTO_ABYTES;

  /* load key and nonce */
  const uint64_t K0 = LOADBYTES(k, 8);
  const uint64_t K1 = LOADBYTES(k + 8, 8);
  const uint64_t N0 = LOADBYTES(npub, 8);
  const uint64_t N1 = LOADBYTES(npub + 8, 8);

  /* initialize */
  ascon_state_t s;
  s.x[0] = ASCON_128_IV;
  s.x[1] = K0;
  s.x[2] = K1;
  s.x[3] = N0;
  s.x[4] = N1;
  printstate("init 1st key xor", &s);
  P12(&s);
  s.x[3] ^= K0;
  s.x[4] ^= K1;
  printstate("init 2nd key xor", &s);

  if (adlen) {
    /* full associated data blocks */
    while (adlen >= ASCON_128_RATE) {
      s.x[0] ^= LOADBYTES(ad, 8);
      printstate("absorb adata", &s);
      P6(&s);
      ad += ASCON_128_RATE;
      adlen -= ASCON_128_RATE;
    }
    /* final associated data block */
    s.x[0] ^= LOADBYTES(ad, adlen);
    s.x[0] ^= PAD(adlen);
    printstate("pad adata", &s);
    P6(&s);
  }
  /* domain separation */
  s.x[4] ^= DSEP();
  printstate("domain separation", &s);

  /* full plaintext blocks */
  while (mlen >= ASCON_128_RATE) {
    s.x[0] ^= LOADBYTES(m, 8);
    STOREBYTES(c, s.x[0], 8);
    printstate("absorb plaintext", &s);
    P6(&s);
    m += ASCON_128_RATE;
    c += ASCON_128_RATE;
    mlen -= ASCON_128_RATE;
  }
  /* final plaintext block */
  s.x[0] ^= LOADBYTES(m, mlen);
  STOREBYTES(c, s.x[0], mlen);
  s.x[0] ^= PAD(mlen);
  c += mlen;
  printstate("pad plaintext", &s);

  /* finalize */
  s.x[1] ^= K0;
  s.x[2] ^= K1;
  printstate("final 1st key xor", &s);
  P12(&s);
  s.x[3] ^= K0;
  s.x[4] ^= K1;
  printstate("final 2nd key xor", &s);

  /* get tag */
  STOREBYTES(c, s.x[3], 8);
  STOREBYTES(c + 8, s.x[4], 8);

  return 0;
}

int crypto_aead_decrypt(unsigned char* m, unsigned long long* mlen,
                        unsigned char* nsec, const unsigned char* c,
                        unsigned long long clen, const unsigned char* ad,
                        unsigned long long adlen, const unsigned char* npub,
                        const unsigned char* k) {
  (void)nsec;

  if (clen < CRYPTO_ABYTES) return -1;

  /* set plaintext size */
  *mlen = clen - CRYPTO_ABYTES;

  /* load key and nonce */
  const uint64_t K0 = LOADBYTES(k, 8);
  const uint64_t K1 = LOADBYTES(k + 8, 8);
  const uint64_t N0 = LOADBYTES(npub, 8);
  const uint64_t N1 = LOADBYTES(npub + 8, 8);

  /* initialize */
  ascon_state_t s;
  s.x[0] = ASCON_128_IV;
  s.x[1] = K0;
  s.x[2] = K1;
  s.x[3] = N0;
  s.x[4] = N1;
  printstate("init 1st key xor", &s);
  P12(&s);
  s.x[3] ^= K0;
  s.x[4] ^= K1;
  printstate("init 2nd key xor", &s);

  if (adlen) {
    /* full associated data blocks */
    while (adlen >= ASCON_128_RATE) {
      s.x[0] ^= LOADBYTES(ad, 8);
      printstate("absorb adata", &s);
      P6(&s);
      ad += ASCON_128_RATE;
      adlen -= ASCON_128_RATE;
    }
    /* final associated data block */
    s.x[0] ^= LOADBYTES(ad, adlen);
    s.x[0] ^= PAD(adlen);
    printstate("pad adata", &s);
    P6(&s);
  }
  /* domain separation */
  s.x[4] ^= DSEP();
  printstate("domain separation", &s);

  /* full ciphertext blocks */
  clen -= CRYPTO_ABYTES;
  while (clen >= ASCON_128_RATE) {
    uint64_t c0 = LOADBYTES(c, 8);
    STOREBYTES(m, s.x[0] ^ c0, 8);
    s.x[0] = c0;
    printstate("insert ciphertext", &s);
    P6(&s);
    m += ASCON_128_RATE;
    c += ASCON_128_RATE;
    clen -= ASCON_128_RATE;
  }
  /* final ciphertext block */
  uint64_t c0 = LOADBYTES(c, clen);
  STOREBYTES(m, s.x[0] ^ c0, clen);
  s.x[0] = CLEARBYTES(s.x[0], clen);
  s.x[0] |= c0;
  s.x[0] ^= PAD(clen);
  c += clen;
  printstate("pad ciphertext", &s);

  /* finalize */
  s.x[1] ^= K0;
  s.x[2] ^= K1;
  printstate("final 1st key xor", &s);
  P12(&s);
  s.x[3] ^= K0;
  s.x[4] ^= K1;
  printstate("final 2nd key xor", &s);

  /* get tag */
  uint8_t t[16];
  STOREBYTES(t, s.x[3], 8);
  STOREBYTES(t + 8, s.x[4], 8);

  /* verify should be constant time, check compiler output */
  int i;
  int result = 0;
  for (i = 0; i < CRYPTO_ABYTES; ++i) result |= c[i] ^ t[i];
  result = (((result - 1) >> 8) & 1) - 1;

  return result;
}
