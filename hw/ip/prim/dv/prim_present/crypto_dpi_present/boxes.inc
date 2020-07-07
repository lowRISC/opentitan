/*
 * S-Boxes and P-Boxes for
 * Implementation of PRESENT in C
 * v2.1, 10/13/2008
 *
 * Implementation is located at http://www.lightweightcrypto.org/implementations.php,
 * under the title "Testvectors for PRESENT".
 *
 * Thomas Siebert, thomas.siebert@rub.de
 */

const uint8_t Sbox[16] = {12, 5, 6, 11, 9, 0, 10, 13, 3, 14, 15, 8, 4, 7, 1, 2};

const uint8_t SboxInv[16] = {5,  14, 15, 8, 12, 1, 2, 13,
                             11, 4,  6,  3, 0,  7, 9, 10};

const uint8_t PboxInv[64] = {0,  16, 32, 48, 1,  17, 33, 49, 2,  18, 34, 50, 3,
                             19, 35, 51, 4,  20, 36, 52, 5,  21, 37, 53, 6,  22,
                             38, 54, 7,  23, 39, 55, 8,  24, 40, 56, 9,  25, 41,
                             57, 10, 26, 42, 58, 11, 27, 43, 59, 12, 28, 44, 60,
                             13, 29, 45, 61, 14, 30, 46, 62, 15, 31, 47, 63};

const uint8_t Pbox[64] = {0,  4,  8,  12, 16, 20, 24, 28, 32, 36, 40, 44, 48,
                          52, 56, 60, 1,  5,  9,  13, 17, 21, 25, 29, 33, 37,
                          41, 45, 49, 53, 57, 61, 2,  6,  10, 14, 18, 22, 26,
                          30, 34, 38, 42, 46, 50, 54, 58, 62, 3,  7,  11, 15,
                          19, 23, 27, 31, 35, 39, 43, 47, 51, 55, 59, 63};
