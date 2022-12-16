#include "config.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "SP800-185.h"
#include "KeccakHash.h"

/**
 * Exit if `condition` is false.
 *
 * @param condition Condition to be checked.
 */
static void assert(int condition)
{
    if (!condition) {
      printf("Condition not satisfied.\n");
      exit(1);
    }
}

/**
 * Print given long byte array with hex characters.
 *
 * @param ptr Byte array pointer.
 * @param len Number of bytes to be printed.
 */
void print_long_array(uint8_t *ptr, size_t len) {
  for (size_t i = 0; i < len; ++i)
    printf("%02x", ptr[i]);
  printf("\n");
}

/**
 * Simple example for XKCP for KMAC test vector generation.
 */
int main(void)
{
    unsigned char output[512 / 8];
    int err_status;

    {
        const BitSequence *key = (const  BitSequence *)
            "\x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4A\x4B\x4C\x4D\x4E\x4F\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5A\x5B\x5C\x5D\x5E\x5F";
        const BitSequence *input = (const  BitSequence *)"\x00\x01\x02\x03";
        const BitSequence *customization = (const  BitSequence *)"";
        const BitSequence *expected_output = (const  BitSequence *)
            "\xE5\x78\x0B\x0D\x3E\xA6\xF7\xD3\xA4\x29\xC5\x70\x6A\xA4\x3A\x00\xFA\xDB\xD7\xD4\x96\x28\x83\x9E\x31\x87\x24\x3F\x45\x6E\xE1\x4E";

        // The KMAC128 function's signature:
        // int KMAC128(const BitSequence *key, BitLength keyBitLen,
        //             const BitSequence *input, BitLength inputBitLen,
        //             BitSequence *output, BitLength outputBitLen,
        //             const BitSequence *customization, BitLength customBitLen);
        //

        err_status = KMAC128(key, /*keyBitLen=*/256, input, /*inputBitLen=*/32,
                             output, /*outputBitLen=*/256, customization, /*customBitLen=*/0);
        assert(err_status == 0);
        assert(memcmp(expected_output, output, sizeof(expected_output)) == 0);
        print_long_array(output, sizeof(output));
    }
    return 0;
}
