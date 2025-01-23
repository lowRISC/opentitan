// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//##############################################
//#  https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
//#  Only testvectors with an IV length of 12 bytes were taken as this IV length is
//#  supported by the AES block.
//###############################################
package nist_vectors_gcm_pkg;

  import uvm_pkg::*;
  import aes_pkg::*;

  typedef struct {
    aes_mode_e   mode;
    key_len_e    key_len;
    aes_op_e     operation;
    int          num_plain_text_blocks;
    int          last_plain_text_block_size;
    int          num_aad_blocks;
    int          last_aad_block_size;
    bit [127:0]  iv;
    bit [255:0]  key;
    bit [3:0] [31:0]  len_ctx_aad;
    bit [3:0] [31:0]  plain_text[4];
    bit [3:0] [31:0]  aad[4];
    bit [3:0] [31:0]  cipher_text[4];
    bit [3:0] [31:0]  tag;
  } nist_vector_gcm_t;



  function automatic string vectorgcm2string(nist_vector_gcm_t vector);
    string              str;
    str = $sformatf("\n ----| NIST GCM Vector | ----");
    str = $sformatf("%s \n Notes that the Nist Vectors are listed in little endian format",
                    str);
    str = $sformatf("%s \n and need to be byteswapped for use with AES", str);
    str = $sformatf("%s \n Mode: %s", str, vector.mode.name);
    str = $sformatf("%s \n Key Len: %s", str, vector.key_len.name);
    str = $sformatf("%s \n Key: %0h", str, vector.key);
    str = $sformatf("%s \n Iv: %0h", str, vector.iv);
    str = $sformatf("%s \n Number of ptx blocks: %0h", str, vector.num_plain_text_blocks);
    str = $sformatf("%s \n Length of last ptx block: %0h", str, vector.last_plain_text_block_size);
    str = $sformatf("%s \n plaintext: %0h", str, vector.plain_text[0]);
    str = $sformatf("%s \n plaintext: %0h", str, vector.plain_text[1]);
    str = $sformatf("%s \n plaintext: %0h", str, vector.plain_text[2]);
    str = $sformatf("%s \n plaintext: %0h", str, vector.plain_text[3]);
    str = $sformatf("%s \n Number of aad blocks: %0h", str, vector.num_aad_blocks);
    str = $sformatf("%s \n Length of last aad block: %0h", str, vector.last_aad_block_size);
    str = $sformatf("%s \n aad: %0h", str, vector.aad[0]);
    str = $sformatf("%s \n aad: %0h", str, vector.aad[1]);
    str = $sformatf("%s \n aad: %0h", str, vector.aad[2]);
    str = $sformatf("%s \n aad: %0h", str, vector.aad[3]);
    str = $sformatf("%s \n len(ad) || len(pt): %0h", str, vector.len_ctx_aad);
    str = $sformatf("%s \n tag: %0h", str, vector.tag[0]);
    str = $sformatf("%s \n tag: %0h", str, vector.tag[1]);
    str = $sformatf("%s \n tag: %0h", str, vector.tag[2]);
    str = $sformatf("%s \n tag: %0h", str, vector.tag[3]);
    str = $sformatf("%s \n ciphertext: %0h", str, vector.cipher_text[0]);
    str = $sformatf("%s \n ciphertext: %0h", str, vector.cipher_text[1]);
    str = $sformatf("%s \n ciphertext: %0h", str, vector.cipher_text[2]);
    str = $sformatf("%s \n ciphertext: %0h", str, vector.cipher_text[3]);
    return str;
  endfunction // vector2string


  class aes_nist_vectors_gcm extends uvm_object;
    `uvm_object_utils(aes_nist_vectors_gcm)
    nist_vector_gcm_t vector_q[];
    int           num;


    function new(string name = "aes_nist_vectors_gcm");
      super.new();
      num = get_num_vectors_gcm();
      vector_q = new[num];
      get_vectors_gcm(vector_q);
    endfunction // new


    function void get_vectors_gcm(ref nist_vector_gcm_t nist_vectors[]);
      // NIST Test Case 1 //
      nist_vectors[0].mode    = AES_GCM;
      nist_vectors[0].key_len = AES_128;
      nist_vectors[0].num_plain_text_blocks = 0;
      nist_vectors[0].last_plain_text_block_size = 0;
      nist_vectors[0].num_aad_blocks = 0;
      nist_vectors[0].last_aad_block_size = 0;
      nist_vectors[0].key  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nist_vectors[0].iv          = 128'h00000000000000000000000000000000;
      nist_vectors[0].len_ctx_aad = 128'h00000000000000000000000000000000;
      nist_vectors[0].plain_text  = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[0].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[0].cipher_text = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[0].tag         = 128'h58e2fccefa7e3061367f1d57a4e7455a;

      // NIST Test Case 2 //
      nist_vectors[1].mode    = AES_GCM;
      nist_vectors[1].key_len = AES_128;
      nist_vectors[1].key  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nist_vectors[1].num_plain_text_blocks = 1;
      nist_vectors[1].last_plain_text_block_size = 16;
      nist_vectors[1].num_aad_blocks = 0;
      nist_vectors[1].last_aad_block_size = 0;

      nist_vectors[1].iv      = 128'h00000000000000000000000000000000;
      nist_vectors[1].len_ctx_aad = 128'h00000000000000000000000000000080;
      nist_vectors[1].plain_text  = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[1].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[1].cipher_text = '{ 128'h0388dace60b6a392f328c2b971b2fe78,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[1].tag         = 128'hab6e47d42cec13bdf53a67b21257bddf;

      // NIST Test Case 3 //
      nist_vectors[2].mode    = AES_GCM;
      nist_vectors[2].key_len = AES_128;
      nist_vectors[2].key  = 256'hfeffe9928665731c6d6a8f946730830800000000000000000000000000000000;
      nist_vectors[2].num_plain_text_blocks = 4;
      nist_vectors[2].last_plain_text_block_size = 16;
      nist_vectors[2].num_aad_blocks = 0;
      nist_vectors[2].last_aad_block_size = 0;
      nist_vectors[2].iv      =     128'hcafebabefacedbaddecaf88800000000;
      nist_vectors[2].len_ctx_aad = 128'h00000000000000000000000000000200;
      nist_vectors[2].plain_text  = '{ 128'hd9313225f88406e5a55909c5aff5269a,
                                       128'h86a7a9531534f7da2e4c303d8a318a72,
                                       128'h1c3c0c95956809532fcf0e2449a6b525,
                                       128'hb16aedf5aa0de657ba637b391aafd255
                                      };
      nist_vectors[2].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[2].cipher_text = '{ 128'h42831ec2217774244b7221b784d0d49c,
                                       128'he3aa212f2c02a4e035c17e2329aca12e,
                                       128'h21d514b25466931c7d8f6a5aac84aa05,
                                       128'h1ba30b396a0aac973d58e091473f5985
                                      };
      nist_vectors[2].tag         = 128'h4d5c2af327cd64a62cf35abd2ba6fab4;

      // NIST Test Case 4 //
      nist_vectors[3].mode    = AES_GCM;
      nist_vectors[3].key_len = AES_128;
      nist_vectors[3].key  = 256'hfeffe9928665731c6d6a8f946730830800000000000000000000000000000000;
      nist_vectors[3].num_plain_text_blocks = 4;
      nist_vectors[3].last_plain_text_block_size = 12;
      nist_vectors[3].num_aad_blocks = 2;
      nist_vectors[3].last_aad_block_size = 4;
      nist_vectors[3].iv      = 128'hcafebabefacedbaddecaf88800000000;
      nist_vectors[3].len_ctx_aad = 128'h00000000000000a000000000000001e0;
      nist_vectors[3].plain_text  = '{ 128'hd9313225f88406e5a55909c5aff5269a,
                                       128'h86a7a9531534f7da2e4c303d8a318a72,
                                       128'h1c3c0c95956809532fcf0e2449a6b525,
                                       128'hb16aedf5aa0de657ba637b3900000000
                                      };
      nist_vectors[3].aad         = '{ 128'hfeedfacedeadbeeffeedfacedeadbeef,
                                       128'habaddad2000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[3].cipher_text = '{ 128'h42831ec2217774244b7221b784d0d49c,
                                       128'he3aa212f2c02a4e035c17e2329aca12e,
                                       128'h21d514b25466931c7d8f6a5aac84aa05,
                                       128'h1ba30b396a0aac973d58e09100000000
                                      };
      nist_vectors[3].tag         = 128'h5bc94fbc3221a5db94fae95ae7121a47;

      // NIST Test Case 7 //
      nist_vectors[4].mode    = AES_GCM;
      nist_vectors[4].key_len = AES_192;
      nist_vectors[4].key  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nist_vectors[4].num_plain_text_blocks = 0;
      nist_vectors[4].last_plain_text_block_size = 0;
      nist_vectors[4].num_aad_blocks = 0;
      nist_vectors[4].last_aad_block_size = 0;
      nist_vectors[4].iv      = 128'h000000000000000000000000;
      nist_vectors[4].len_ctx_aad = 128'h00000000000000000000000000000000;
      nist_vectors[4].plain_text  = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[4].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[4].cipher_text = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[4].tag         = 128'hcd33b28ac773f74ba00ed1f312572435;

      // NIST Test Case 8 //
      nist_vectors[5].mode    = AES_GCM;
      nist_vectors[5].key_len = AES_192;
      nist_vectors[5].key  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nist_vectors[5].num_plain_text_blocks = 1;
      nist_vectors[5].last_plain_text_block_size = 16;
      nist_vectors[5].num_aad_blocks = 0;
      nist_vectors[5].last_aad_block_size = 0;
      nist_vectors[5].iv      = 128'h000000000000000000000000;
      nist_vectors[5].len_ctx_aad = 128'h00000000000000000000000000000080;
      nist_vectors[5].plain_text  = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[5].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[5].cipher_text = '{ 128'h98e7247c07f0fe411c267e4384b0f600,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[5].tag         = 128'h2ff58d80033927ab8ef4d4587514f0fb;

      // NIST Test Case 9 //
      nist_vectors[6].mode    = AES_GCM;
      nist_vectors[6].key_len = AES_192;
      nist_vectors[6].key  = 256'hfeffe9928665731c6d6a8f9467308308feffe9928665731c0000000000000000;
      nist_vectors[6].num_plain_text_blocks = 4;
      nist_vectors[6].last_plain_text_block_size = 16;
      nist_vectors[6].num_aad_blocks = 0;
      nist_vectors[6].last_aad_block_size = 0;
      nist_vectors[6].iv      = 128'hcafebabefacedbaddecaf88800000000;
      nist_vectors[6].len_ctx_aad = 128'h000000000000000000000000000000200;
      nist_vectors[6].plain_text  = '{ 128'hd9313225f88406e5a55909c5aff5269a,
                                       128'h86a7a9531534f7da2e4c303d8a318a72,
                                       128'h1c3c0c95956809532fcf0e2449a6b525,
                                       128'hb16aedf5aa0de657ba637b391aafd255
                                      };
      nist_vectors[6].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[6].cipher_text = '{ 128'h3980ca0b3c00e841eb06fac4872a2757,
                                       128'h859e1ceaa6efd984628593b40ca1e19c,
                                       128'h7d773d00c144c525ac619d18c84a3f47,
                                       128'h18e2448b2fe324d9ccda2710acade256
                                      };
      nist_vectors[6].tag         = 128'h9924a7c8587336bfb118024db8674a14;

      // NIST Test Case 10 //
      nist_vectors[7].mode    = AES_GCM;
      nist_vectors[7].key_len = AES_192;
      nist_vectors[7].key  = 256'hfeffe9928665731c6d6a8f9467308308feffe9928665731c0000000000000000;
      nist_vectors[7].num_plain_text_blocks = 4;
      nist_vectors[7].last_plain_text_block_size = 12;
      nist_vectors[7].num_aad_blocks = 2;
      nist_vectors[7].last_aad_block_size = 12;
      nist_vectors[7].iv      = 128'hcafebabefacedbaddecaf88800000000;
      nist_vectors[7].len_ctx_aad = 128'h00000000000000a000000000000001e0;
      nist_vectors[7].plain_text  = '{ 128'hd9313225f88406e5a55909c5aff5269a,
                                       128'h86a7a9531534f7da2e4c303d8a318a72,
                                       128'h1c3c0c95956809532fcf0e2449a6b525,
                                       128'hb16aedf5aa0de657ba637b3900000000
                                      };
      nist_vectors[7].aad         = '{ 128'hfeedfacedeadbeeffeedfacedeadbeef,
                                       128'habaddad2000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[7].cipher_text = '{ 128'h3980ca0b3c00e841eb06fac4872a2757,
                                       128'h859e1ceaa6efd984628593b40ca1e19c,
                                       128'h7d773d00c144c525ac619d18c84a3f47,
                                       128'h18e2448b2fe324d9ccda271000000000
                                      };
      nist_vectors[7].tag         = 128'h2519498e80f1478f37ba55bd6d27618c;

      // NIST Test Case 13 //
      nist_vectors[8].mode    = AES_GCM;
      nist_vectors[8].key_len = AES_256;
      nist_vectors[8].key  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nist_vectors[8].num_plain_text_blocks = 0;
      nist_vectors[8].last_plain_text_block_size = 0;
      nist_vectors[8].num_aad_blocks = 0;
      nist_vectors[8].last_aad_block_size = 0;
      nist_vectors[8].iv      = 128'h00000000000000000000000000000000;
      nist_vectors[8].len_ctx_aad = 128'h00000000000000000000000000000000;
      nist_vectors[8].plain_text  = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[8].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[8].cipher_text = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[8].tag         = 128'h530f8afbc74536b9a963b4f1c4cb738b;

      // NIST Test Case 14 //
      nist_vectors[9].mode    = AES_GCM;
      nist_vectors[9].key_len = AES_256;
      nist_vectors[9].key  = 256'h0000000000000000000000000000000000000000000000000000000000000000;
      nist_vectors[9].num_plain_text_blocks = 1;
      nist_vectors[9].last_plain_text_block_size = 16;
      nist_vectors[9].num_aad_blocks = 0;
      nist_vectors[9].last_aad_block_size = 0;
      nist_vectors[9].iv      = 128'h00000000000000000000000000000000;
      nist_vectors[9].len_ctx_aad = 128'h00000000000000000000000000000080;
      nist_vectors[9].plain_text  = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[9].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[9].cipher_text = '{ 128'hcea7403d4d606b6e074ec5d3baf39d18,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[9].tag         = 128'hd0d1c8a799996bf0265b98b5d48ab919;

      // NIST Test Case 15 //
      nist_vectors[10].mode    = AES_GCM;
      nist_vectors[10].key_len = AES_256;
      nist_vectors[10].key  = 256'hfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308;
      nist_vectors[10].num_plain_text_blocks = 4;
      nist_vectors[10].last_plain_text_block_size = 16;
      nist_vectors[10].num_aad_blocks = 0;
      nist_vectors[10].last_aad_block_size = 0;
      nist_vectors[10].iv      = 128'hcafebabefacedbaddecaf88800000000;
      nist_vectors[10].len_ctx_aad = 128'h00000000000000000000000000000200;
      nist_vectors[10].plain_text  = '{ 128'hd9313225f88406e5a55909c5aff5269a,
                                       128'h86a7a9531534f7da2e4c303d8a318a72,
                                       128'h1c3c0c95956809532fcf0e2449a6b525,
                                       128'hb16aedf5aa0de657ba637b391aafd255
                                      };
      nist_vectors[10].aad         = '{ 128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[10].cipher_text = '{ 128'h522dc1f099567d07f47f37a32a84427d,
                                       128'h643a8cdcbfe5c0c97598a2bd2555d1aa,
                                       128'h8cb08e48590dbb3da7b08b1056828838,
                                       128'hc5f61e6393ba7a0abcc9f662898015ad
                                      };
      nist_vectors[10].tag         = 128'hb094dac5d93471bdec1a502270e3cc6c;

      // NIST Test Case 16 //
      nist_vectors[11].mode    = AES_GCM;
      nist_vectors[11].key_len = AES_256;
      nist_vectors[11].key  = 256'hfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308;
      nist_vectors[11].num_plain_text_blocks = 4;
      nist_vectors[11].last_plain_text_block_size = 12;
      nist_vectors[11].num_aad_blocks = 2;
      nist_vectors[11].last_aad_block_size = 4;
      nist_vectors[11].iv      = 128'hcafebabefacedbaddecaf88800000000;
      nist_vectors[11].len_ctx_aad = 128'h00000000000000a000000000000001e0;
      nist_vectors[11].plain_text  = '{ 128'hd9313225f88406e5a55909c5aff5269a,
                                       128'h86a7a9531534f7da2e4c303d8a318a72,
                                       128'h1c3c0c95956809532fcf0e2449a6b525,
                                       128'hb16aedf5aa0de657ba637b3900000000
                                      };
      nist_vectors[11].aad         = '{ 128'hfeedfacedeadbeeffeedfacedeadbeef,
                                       128'habaddad2000000000000000000000000,
                                       128'h00000000000000000000000000000000,
                                       128'h00000000000000000000000000000000
                                      };
      nist_vectors[11].cipher_text = '{ 128'h522dc1f099567d07f47f37a32a84427d,
                                       128'h643a8cdcbfe5c0c97598a2bd2555d1aa,
                                       128'h8cb08e48590dbb3da7b08b1056828838,
                                       128'hc5f61e6393ba7a0abcc9f66200000000
                                      };
      nist_vectors[11].tag         = 128'h76fc6ece0f4e1768cddf8853bb2d551b;

    endfunction

    function int get_num_vectors_gcm();
      return 12;
    endfunction

  endclass
endpackage
