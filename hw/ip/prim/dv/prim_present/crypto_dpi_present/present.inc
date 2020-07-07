/*
 * Implementation of PRESENT in C
 * v2.1, 10/13/2008
 *
 * Implementation is located at http://www.lightweightcrypto.org/implementations.php,
 * under the title "Testvectors for PRESENT".
 *
 * Thomas Siebert, thomas.siebert@rub.de
 *
 *
 * Your Compiler currently should support
 * the ANSI-C99-standard.
 *
 * Tested with gcc (with Option -std=c99)
 */

//----------------------------------
// Includes
//----------------------------------
#include "verbose.inc"  //For verbose output
#include "comline.inc"  //Command Line
#include "boxes.inc"    //S-Boxes and P-Boxes
#include <stdlib.h>

//----------------------------------
// Macros for bit manipulation
//----------------------------------
//returns...
#define high45_64(h45in) ((uint64_t)h45in >> 9)            // 45 msb as lsb
#define high61_64(h4in) ((uint64_t)h4in >> 3)              // 61 msb as lsb
#define high4_64(h4in) ((uint64_t)h4in >> 60)              // 4 msb as lsb
#define high8to4_64(h8in) (((uint64_t)h8in >> 56) & 0x0F)  // 4 msb as 2. lsb
#define high16_64(h16in) ((uint64_t)h16in >> 48)           // 16 msb as lsb
#define high1_64(h1in) ((uint64_t)h1in >> 63)              // msb as lsb
#define low4_64(l4in) ((uint64_t)l4in << 60)               // 4 lsb as msb
#define low8to4_64(l4in) ((uint64_t)l4in << 56)            // 4 lsb as 2. msb
#define low16_64(l4in) ((uint64_t)l4in << 48)              // 4 lsb as msb
#define rotate1l_64(r1lin) \
  (high1_64(r1lin) | (r1lin << 1))  // input rotated left (1x)
#define rotate1r_64(r1rin) \
  (high1_64(r1rin) | (r1rin >> 1))  // input rotated right (1x)
#define rotate4l_64(r4lin) \
  (high4_64(r4lin) | (r4lin << 4))  // input rotated left (4x)
#define rotate4r_64(r4rin) \
  (high4_64(r4rin) | (r4rin >> 4))  // input rotated right (4x)

//----------------------------------
// Function prototypes
//----------------------------------
uint64_t encrypt(uint64_t, uint64_t *, uint16_t, _Bool);
uint64_t decrypt(uint64_t, uint64_t *, uint16_t, _Bool);
uint64_t *key_schedule(uint64_t, uint64_t, uint16_t, _Bool, _Bool);

// We have commented out the main(...) function of the C model as the testbench is directly
// calling encrypt(), decrypt(), and key_schedule() functions.
// It also contains unnecessary command line parsing functionality that is not needed for
// the testbench.
//
//----------------------------------
// Start of code
//----------------------------------
// int main( int argc, char ** const argv )
//{
//	// Initialize variables
//	uint64_t result;
//	struct Options Opt;
//
//	// Get Commandline Options
//	comline_fetch_options( &Opt, argc, argv );
//
//	// Banner
//	if ( Opt.Verbose != 0 )
//	{
//		printf( "---------------------------------------\n" );
//		printf( "PRESENT Commandline Tool v2.1\n" );
//		printf( "Thomas Siebert, thomas.siebert@rub.de\n" );
//		printf( "---------------------------------------\n\n" );
//	}
//
//	if ( !Opt.Error )
//	{
//		uint64_t *subkey;
//
//		if ( Opt.Mode == Encrypt_Mode )
//		{
//			// Put out Values
//			if ( Opt.Verbose != 0 )
//			{
//				printf( "Starting values\n" );
//				printf( "Plaintext: %016"PRIx64" \n", Opt.Text);
//				if (Opt.KeySize80) printf( "Given Key (80bit):
//%016"PRIx64" %04"PRIx64"\n\n", Opt.KeyHigh, (Opt.KeyLow&0xFFFF) ); 				else
//printf( "Given Key (128bit): %016"PRIx64" %016"PRIx64"\n\n", Opt.KeyHigh,
//Opt.KeyLow );
//			}
//
//			// Generate Subkeys
//			subkey=key_schedule( Opt.KeyHigh, Opt.KeyLow, Opt.Rounds,
//Opt.KeySize80, (Opt.Verbose>1) );
//
//			// Start Encryption
//			if ( Opt.Verbose != 0 )	printf( "Starting
//encryption...\n" ); 			result=encrypt(Opt.Text, subkey, Opt.Rounds,
//(Opt.Verbose>1) ); 			if ( Opt.Verbose != 0 )	printf( "Resulting Cipher:
//%016"PRIx64" \n\n", result); 			else printf( "%016"PRIx64"\n", result);
//		}
//
//		else if ( Opt.Mode == Decrypt_Mode )
//		{
//			// Put out Values
//			if ( Opt.Verbose != 0 )
//			{
//				printf( "Starting values\n" );
//				printf( "Ciphertext: %016"PRIx64" \n",
//Opt.Text); 				if (Opt.KeySize80) printf( "Given Key (80bit): %016"PRIx64"
//%04"PRIx64"\n\n", Opt.KeyHigh, (Opt.KeyLow&0xFFFF) ); 				else printf( "Given Key
//(128bit): %016"PRIx64" %016"PRIx64"\n\n", Opt.KeyHigh, Opt.KeyLow );
//			}
//
//			// Generate Subkeys
//			subkey=key_schedule( Opt.KeyHigh, Opt.KeyLow, Opt.Rounds,
//Opt.KeySize80, (Opt.Verbose>1) );
//
//			// Start Decryption
//			if ( Opt.Verbose != 0 )	printf( "Starting
//decryption...\n" ); 			result=decrypt(Opt.Text, subkey, Opt.Rounds,
//(Opt.Verbose>1) ); 			if ( Opt.Verbose != 0 )	printf( "Resulting Plaintext:
//%016"PRIx64" \n", result); 			else printf( "%016"PRIx64"\n", result);
//		}
//
//		free(subkey);
//
//	}
//
//	else
//	{
//			// Put out Syntax
//			printf( "Syntax:\n");
//			printf( "PRESENT -d|e [-f] [-r rounds] [-v level] -k key -t
//text\n\n"); 			printf( "Choose -d to decrypt, or -e to encrypt one block\n\n");
//			printf( "-f (optional): File input, see below\n");
//			printf( "-r rounds (optional): Change number of rounds (up
//to 65534, standard is 32)\n"); 			printf( "-v level (optional): Specify verbose
//level:\n"); 			printf( "   0 for result-output only\n"); 			printf( "   1 for output
//of mode, input, result (standard)\n"); 			printf( "   2 for roundwise
//output\n\n"); 			printf( "-k key: Key in hexadecimal (length: *EXACTLY* 20
//chars(80bit)/32 chars(128bit))\n"); 			printf( "-t text: Text in hexadecimal
//(length: *EXACTLY* 16 chars)\n"); 			printf( "If -f is set, key and text
//represent files containing the values,\n"); 			printf( "otherwise they must be
//passed directly via commandline.\n\n"); 			printf( "Returned Errorlevel: 0 if
//successful, 1 if non-successful\n");
//	}
//	return Opt.Error;
//}

//----------------------------------
// Key Scheduling
//----------------------------------
uint64_t *key_schedule(uint64_t key_high, uint64_t key_low, uint16_t Rounds,
                       _Bool KeySize80, _Bool Output) {
  uint64_t temp64;
  uint64_t i;

  uint64_t *subkey = (uint64_t *)malloc(Rounds * sizeof(uint64_t));

  if (subkey != NULL) {
    if (Output)
      v_key_start();

    if (KeySize80) {
      key_low &= 0xFFFF;

      if (Output)
        v_k80_init(key_high, key_low);

      for (i = 0; i < Rounds; i++) {
        subkey[i] = key_high;

        //----------------------------------
        // Shift
        //----------------------------------
        temp64 = key_high;
        key_high <<= 61;
        key_high |= (key_low << 45);
        key_high |= (temp64 >> 19);
        key_low = (temp64 >> 3) & 0xFFFF;

        if (Output && (i + 2 <= Rounds))
          v_k80_shift(key_high, key_low);

        //----------------------------------
        // S-Box
        //----------------------------------
        temp64 = high4_64(key_high);     // get highest nibble
        key_high &= 0x0FFFFFFFFFFFFFFF;  // kill highest nibble
        temp64 = Sbox[temp64];
        key_high |= low4_64(temp64);  // put new value to highest nibble (sbox)

        if (Output && (i + 2 <= Rounds))
          v_k80_sbox(key_high, key_low);

        //----------------------------------
        // Round Salt
        //----------------------------------
        key_low ^= (((i + 1) & 0x01) << 15);
        key_high ^= ((i + 1) >> 1);

        if (Output && (i + 2 <= Rounds))
          v_k80_round(key_high, key_low, i);
      }
    } else  // 128 Bit
    {
      if (Output)
        v_k128_init(key_high, key_low);

      for (i = 0; i < Rounds; i++) {
        subkey[i] = key_high;

        //----------------------------------
        // Shift
        //----------------------------------
        temp64 = high61_64(key_high);
        key_high <<= 61;
        key_high |= high61_64(key_low);
        key_low <<= 61;
        key_low |= temp64;

        if (Output && (i + 2 <= Rounds))
          v_k128_shift(key_high, key_low);

        //----------------------------------
        // S-Box
        //----------------------------------
        temp64 = high4_64(key_high);     // get highest nibble
        key_high &= 0x0FFFFFFFFFFFFFFF;  // kill highest nibble
        temp64 = Sbox[temp64];
        key_high |= low4_64(temp64);  // put new value to highest nibble (sbox)
        temp64 = high8to4_64(key_high);  // get 2. highest nibble
        key_high &= 0xF0FFFFFFFFFFFFFF;  // kill 2. highest nibble
        temp64 = Sbox[temp64];
        key_high |=
            low8to4_64(temp64);  // put new value to 2. highest nibble (sbox)

        if (Output && (i + 2 <= Rounds))
          v_k128_sbox(key_high, key_low);

        //----------------------------------
        // Round Salt
        //----------------------------------
        key_low ^= (((i + 1) & 0x03) << 62);  // add counter to lower key part
        key_high ^= ((i + 1) >> 2);           // add counter to higher key part

        if (Output && (i + 2 <= Rounds))
          v_k128_round(key_high, key_low, i);
      }
    }
    if (Output)
      v_final();
  } else {
    printf("RAM problem!\n");
    exit(0);
  }
  return subkey;
}

//----------------------------------
// Encryption
//----------------------------------
uint64_t encrypt(uint64_t in, uint64_t *subkey, uint16_t Rounds,
                 _Bool Roundwise) {  // Start encryption

#define out in
  uint16_t RoundNr;
  uint64_t text;

  if (Roundwise)
    v_enc_start(in);

  for (RoundNr = 1; RoundNr < Rounds; RoundNr++) {  // Start "for"
    uint16_t temp;
#define SboxNr temp
#define PBit temp

    if (Roundwise)
      v_roundstart(RoundNr, subkey[RoundNr - 1]);

    //----------------------------------
    // Xor with roundkey
    //----------------------------------
    text = in ^ subkey[RoundNr - 1];

    if (Roundwise)
      v_after_xor(text);

    //----------------------------------
    // S-Boxes
    //----------------------------------
    for (SboxNr = 0; SboxNr < 16; SboxNr++) {
      uint16_t SboxVal;

      SboxVal = text & 0x0F;       // get lowest nibble
      text &= 0xFFFFFFFFFFFFFFF0;  // kill lowest nibble
      text |= Sbox[SboxVal];       // put new value to lowest nibble (sbox)
      text = rotate4l_64(text);    // next(rotate by one nibble)
    }

    if (Roundwise)
      v_after_s(text);

    //----------------------------------
    // P-Box
    //----------------------------------
    for (PBit = 0, out = 0; PBit < 64; PBit++) {
      out = rotate1l_64(out);  // next(rotate by one bit)
      out |= ((text >> 63 - Pbox[PBit]) &
              1);  // put new value to lowest bit (pbox)
    }

    if (Roundwise)
      v_after_p(in);

  }  // End "for"

  text = in ^ subkey[RoundNr - 1];

  if (Roundwise)
    v_enc_final(text, subkey[RoundNr - 1]);

  return text;

}  // End encryption

//----------------------------------
// Decryption
//----------------------------------
uint64_t decrypt(uint64_t in, uint64_t *subkey, uint16_t Rounds,
                 _Bool Roundwise) {  // Start decryption
#define out in
  uint16_t RoundNr;
  uint64_t text;

  if (Roundwise)
    v_dec_start(in);

  for (RoundNr = 1; RoundNr <= Rounds; RoundNr++) {  // Start "for"
    uint64_t key_temp;
    uint16_t temp;
#define SboxNr temp
#define PBit temp

    if (Roundwise)
      v_roundstart(RoundNr, subkey[Rounds - RoundNr]);

    //----------------------------------
    // Xor with roundkey
    //----------------------------------
    text = in ^ subkey[Rounds - RoundNr];

    if (Roundwise)
      v_after_xor(text);

    //----------------------------------
    // P-Box
    //----------------------------------
    for (PBit = 0, out = 0; PBit < 64; PBit++) {
      out = rotate1l_64(out);  // next(rotate by one bit)
      out |= ((text >> 63 - PboxInv[PBit]) &
              1);  // put new value to lowest bit (pbox)
    }

    if (Roundwise)
      v_after_p(out);

    //----------------------------------
    // S-Boxes
    //----------------------------------
    for (SboxNr = 0; SboxNr < 16; SboxNr++) {
      uint16_t SboxVal;

      SboxVal = out & 0x0F;
      out &= 0xFFFFFFFFFFFFFFF0;
      out |= SboxInv[SboxVal];
      out = rotate4l_64(out);
    }

    if (Roundwise)
      v_after_s(out);

  }  // End "for"

  if (Roundwise)
    v_final();

  return text;

}  // End decryption
