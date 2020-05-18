/*
 * Verbose-Functions for
 * Implementation of PRESENT in C
 * v2.1, 10/13/2008
 *
 * Implementation is located at http://www.lightweightcrypto.org/implementations.php,
 * under the title "Testvectors for PRESENT".
 *
 * Thomas Siebert, thomas.siebert@rub.de
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

//----------------------------------
// Function prototypes
//----------------------------------
void v_enc_start(uint64_t);
void v_enc_final(uint64_t, uint64_t);
void v_dec_start(uint64_t);
void v_roundstart(uint16_t, uint64_t);
void v_after_xor(uint64_t);
void v_after_s(uint64_t);
void v_after_p(uint64_t);
void v_final(void);
void v_k80_init(uint64_t, uint64_t);
void v_k80_shift(uint64_t, uint64_t);
void v_k80_sbox(uint64_t, uint64_t);
void v_k80_round(uint64_t, uint64_t, uint16_t);
void v_k128_init(uint64_t, uint64_t);
void v_k128_shift(uint64_t, uint64_t);
void v_k128_sbox(uint64_t, uint64_t);
void v_k128_round(uint64_t, uint64_t, uint16_t);
void v_key_start(void);

//----------------------------------
// Functions
//----------------------------------
void v_enc_start(uint64_t v_plain) {
  printf("************************************\n");
  printf("Verbose output of PRESENT-encryption\n");
  printf("************************************\n\n");
  printf("Given Plaintext: %016" PRIx64 " \n\n", v_plain);
}

void v_dec_start(uint64_t v_plain) {
  printf("************************************\n");
  printf("Verbose output of PRESENT-decryption\n");
  printf("************************************\n\n");
  printf("Given Ciphertext: %016" PRIx64 " \n", v_plain);
}

void v_roundstart(uint16_t v_round, uint64_t v_key) {
  printf("--------------------------------------\n");
  printf("Round %" PRIu16 "\n", v_round);
  printf("Subkey: %016" PRIx64 "\n\n", v_key);
  printf("Text after...\n");
}

void v_enc_final(uint64_t v_final_text, uint64_t v_key) {
  printf("--------------------------------------\n");
  printf("Final Round\n\n");
  printf("Subkey: %016" PRIx64 "\n", v_key);
  printf("Text: %016" PRIx64 " \n\n", v_final_text);
  v_final();
}

void v_final(void) {
  printf("************************************\n");
  printf("End of verbose output\n");
  printf("************************************\n");
}

void v_after_xor(uint64_t v_xor) {
  printf("...Key-Xor: %016" PRIx64 " \n", v_xor);
}

void v_after_s(uint64_t v_s) { printf(".....S-Box: %016" PRIx64 " \n", v_s); }

void v_after_p(uint64_t v_p) { printf(".....P-Box: %016" PRIx64 " \n", v_p); }

void v_k128_init(uint64_t key_high, uint64_t key_low) {
  printf("Input: %016" PRIx64 " %016" PRIx64 "\n\n", key_high, key_low);
  printf("Subkey Round 1: >>%016" PRIx64 "<<\n\n", key_high);
}

void v_k128_shift(uint64_t key_high, uint64_t key_low) {
  printf("...after Shift: %016" PRIx64 " %016" PRIx64 "\n", key_high, key_low);
}

void v_k128_sbox(uint64_t key_high, uint64_t key_low) {
  printf("...after S-Box: %016" PRIx64 " %016" PRIx64 "\n", key_high, key_low);
}

void v_k128_round(uint64_t key_high, uint64_t key_low, uint16_t i) {
  printf("Subkey Round %" PRIu16 " (after Salt): >>%016" PRIx64 "<< %016" PRIx64
         "\n\n",
         i + 2, key_high, key_low);
}

void v_k80_init(uint64_t key_high, uint64_t key_low) {
  printf("Input: %016" PRIx64 " %04" PRIx64 "\n\n", key_high,
         (key_low & 0xFFFF));
  printf("Subkey Round 1: >>%016" PRIx64 "<<\n\n", key_high);
}

void v_k80_shift(uint64_t key_high, uint64_t key_low) {
  printf("...after Shift: %016" PRIx64 " %04" PRIx64 "\n", key_high, key_low);
}

void v_k80_sbox(uint64_t key_high, uint64_t key_low) {
  printf("...after S-Box: %016" PRIx64 " %04" PRIx64 "\n", key_high, key_low);
}

void v_k80_round(uint64_t key_high, uint64_t key_low, uint16_t i) {
  printf("Subkey Round %" PRIu16 " (after Salt): >>%016" PRIx64 "<< %04" PRIx64
         "\n\n",
         i + 2, key_high, key_low);
}
void v_key_start(void) {
  printf("**************************************\n");
  printf("Verbose output of PRESENT-Key-Schedule\n");
  printf("**************************************\n\n");
}
