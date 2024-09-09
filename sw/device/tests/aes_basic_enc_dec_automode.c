// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kTestTimeout = (1000 * 1000),
};



  

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.


static const uint8_t kKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};


OTTF_DEFINE_TEST_CONFIG();

status_t execute_test(void) {
  
  // Initialise AES.
  dif_aes_t aes;
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[sizeof(kAesModesKey128)];
  for (int i = 0; i < sizeof(kAesModesKey128); ++i) {
    key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(key.share0));
  memcpy(key.share1, kKeyShare1, sizeof(key.share1));

 dif_aes_iv_t iv;
  memcpy(iv.iv, kAesModesIvCbc, sizeof(iv.iv));
  

  // Write the initial key share, IV and data in CSRs (known combinations).
 
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  // CHECK_STATUS_OK(aes_testutils_setup_encryption(transaction, aes));
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, &iv));

 
  // "Convert" plain data byte arrays to `dif_aes_data_t` array.
  enum {
    kAesNumBlocks = 4,
  };

  dif_aes_data_t plain_text[kAesNumBlocks];
  dif_aes_data_t cipher_text[kAesNumBlocks];
  memcpy(plain_text[0].data, kAesModesPlainText, sizeof(kAesModesPlainText));

  // Encrypt kAesNumBlocks blocks.
  //  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
  //                              kTestTimeout);
  CHECK_DIF_OK(dif_aes_process_data(&aes, plain_text, cipher_text,
                                    (size_t)kAesNumBlocks));
   CHECK_DIF_OK(dif_aes_load_data(&aes, plain_text[0]));
 
  // Check the produced cipher text.
  ////CHECK_ARRAYS_EQ((uint8_t *)cipher_text[0].data, kAesModesCipherTextEcb128,
   //            sizeof(kAesModesCipherTextEcb128));
   

  LOG_INFO("Started  AES Encrypt with load function");

 

  bool ready = false;

do {
      CHECK_DIF_OK(
          dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
    } while (!ready);


   CHECK_DIF_OK(dif_aes_end(&aes));

 // Check the ciphertext against the expected value.
   CHECK_ARRAYS_EQ((uint8_t *)cipher_text[0].data, kAesModesCipherTextCbc128,
                  sizeof(kAesModesCipherTextCbc128));


   // CHECK_DIF_OK(dif_aes_end(&aes));
// Encryption started

   // CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, &iv));
   // Decrypt operation below
   
 dif_aes_transaction_t transactiond = {
      .operation = kDifAesOperationDecrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

// Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
 //uint8_t key_share0[sizeof(kAesModesKey128)];
  for (int i = 0; i < sizeof(kAesModesKey128); ++i) {
    key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  //dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(key.share0));
  memcpy(key.share1, kKeyShare1, sizeof(key.share1));

  // dif_aes_iv_t iv;
  memcpy(iv.iv, kAesModesIvCbc, sizeof(iv.iv));


     do {
          CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusInputReady, &ready));
        }
     while (!ready);


  
  //Start 
   CHECK_DIF_OK(dif_aes_start(&aes, &transactiond, &key, &iv));
   

   memcpy(cipher_text[0].data, kAesModesCipherTextCbc128,
         sizeof(cipher_text[0].data));

  
     CHECK_DIF_OK(dif_aes_load_data(&aes, cipher_text[0]));
 
     do {
          CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
        }
     while (!ready);

   dif_aes_data_t out_data2;
   CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data2));

   CHECK_DIF_OK(dif_aes_end(&aes));
  // Finish the CBC decryption transaction.
   //CHECK_DIF_OK(dif_aes_end(&aes));
    CHECK_ARRAYS_EQ((uint8_t *)out_data2.data, kAesModesPlainText,
                      sizeof(out_data2.data));
   
//// transaction.manual_operation = kDifAesManualOperationManual;
     // Write the KEY_IV_DATA_IN_CLEAR and DATA_OUT_CLEAR trigger bits to 1 and
  // wait for it to complete by polling the status idle bit.
    //CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerDataOutClear));
//CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerKeyIvDataInClear));
////AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);

     
   //Decrypt
  //transaction.operation =kDifAesOperationDecrypt;
     
   
  return OK_STATUS();
}

bool test_main(void) {
  // Test seed generation using CSRNG SW application interface.
  //
  // We try to generate the seed leading to an all-zero output of the AES
  // masking PRNG using the CSRNG SW application interface. Unlike the HW
  // application interfaces of CSRNG that connect to the EDNs, this interface
  // allows for probing the internal state of the CSRNG instance after
  // individual commands. This gives us higher visibility. If for some reason
  // this phase isn't succesful, we don't even need to try it on the HW
  // interfaces.
  LOG_INFO("Testing AES Encrypt and Decrypt");

  // Disable EDN connected to AES as well as CSRNG.
  // const dif_edn_t edn = {
  //     .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  //const dif_csrng_t csrng = {
  //    .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  //CHECK_DIF_OK(dif_edn_stop(&edn));
  //CHECK_DIF_OK(dif_csrng_stop(&csrng));

  // Re-enable CSRNG.
  //CHECK_DIF_OK(dif_csrng_configure(&csrng));

  return status_ok(execute_test());
}
