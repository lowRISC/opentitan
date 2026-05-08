/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for the KMAC-OTBN interface model.
 */

.section .text.start

kmac_test:
  li x29, 100
  bn.xor w31, w31, w31
  /* Start SHA3-224 test. */
  jal     x1,  sha224_test
  /* Start SHA3-256 test. */
  jal     x1,  sha256_test
  /* Start SHA3-384 test. */
  jal     x1,  sha384_test
  /* Start SHA3-512 test. */
  jal     x1,  sha512_test
  /* Start SHAKE-128 test. */
  jal     x1,  shake128_test
  /* Start SHAKE-256 test. */
  jal     x1,  shake256_test

  ecall

/**
 * Run a SHA3-224 test vector.
 *
 * Len = 456
 * Msg = d505d1039792f0974c62ed94b44920877e465a87b0586eb04892f0d423723c6c1f6fbad57dd161b989c57acb7cb1a7b7a1c52358b7d34b2c97
 * MD = 454d727819bdbeda5a4c3e59bc85a69490d7352ff82ffea00cbc5324
 *
 * This vector stems from the "CAVP Testing: Secure Hashing" test vectors.
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bittestvectors.zip
 *
 * The message and digest from the test vector set are interpreted in little-endian order.
 *
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
sha224_test:
  /**
  * Set x10 to the desired KMAC_CFG.
  * x10 <= 0x2.
  * Bit  [   0] kmac_en   = 0x0
  * Bits [ 3:1] kstrength = 0x1 (L224)
  * Bits [ 5:4] mode      = 0x0 (SHA3)
  */
  li      x10, 0x2

  /* Set pointers to the SHA3-224 test vector. */
  la      x11, sha224_msg_len
  la      x12, sha224_msg
  la      x13, sha224_digest_len
  la      x14, sha224_rate
  la      x15, sha224_digest

  /* Run the test for the SHA3-224 test vector. */
  jal     x1,  run_kmac_test_vector

  ret

/**
 * Run a SHA3-256 test vector.
 *
 * Len = 8
 * Msg = 6a
 * MD = f35e560e05de779f2669b9f513c2a7ab81dfeb100e2f4ee1fb17354bfa2740ca
 *
 * This vector stems from the "CAVP Testing: Secure Hashing" test vectors.
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bittestvectors.zip
 *
 * The message and digest from the test vector set are interpreted in little-endian order.
 *
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
sha256_test:
  /**
  * Set x10 to the desired KMAC_CFG.
  * x10 <= 0x4.
  * Bit  [   0] kmac_en   = 0x0
  * Bits [ 3:1] kstrength = 0x2 (L256)
  * Bits [ 5:4] mode      = 0x0 (SHA3)
  */
  li      x10, 0x4

  /* Set pointers to the SHA3-256 test vector. */
  la      x11, sha256_msg_len
  la      x12, sha256_msg
  la      x13, sha256_digest_len
  la      x14, sha256_rate
  la      x15, sha256_digest

  /* Run the test for the SHA3-256 test vector. */
  jal     x1,  run_kmac_test_vector

  ret

/**
 * Run a SHA3-384 test vector.
 *
 * Len = 7496
 * Msg = 2e5d4a05836654ba2968b795ca2f9f621093165672fb77aa4d20258936147c2c8f8208445837f59848e1c7ef1c174c30309acec84cdb8c4cc0bd6c5fb39bead7b88d541ba2e739cf9a031fb46e4174c92c4bc7b7f09e386bfa462d0503e847f1d10695530a7f07a9465525ac67b300762d2f69ea054c62512243d241cf037dc3047632b43706466c7460429eb077d97f5bcc1d2b34eef244613cc2dcbff2729577649506d284e0614eaade53f195e52cddad4940258acf8ddfba659e7abf10af525825118202bcd0f9bd6294d1130ec5dc5757f27f2be374c344234ea9723d58beda4a9df086c201a0213427f8fb3b917f54ad09ead61540366364b6f311e3d9e3736c71c31bda3b695cbed40f5554d9ef2ab54d10954d3b5f9e909c01a6e97ae8aaf356a4c6ecc87cf86765be2740e55364d586966f73ab677d0fc97a383783f50848143b91e0ee027d96a0ac7be9fdd487777b276d70d97588490507d0b53c3414d1732f839ef62371b54f825836699a1d02f569952a0db248a71750754bedcb56f73b29a40f28065e2b38e7c70f70ccaedebc04f18a8f45448fc9fc2fe1dde2562233d0fd19cbd4cb602484ce5c5c92c07298a18978a657046ae1b4065f55a29dbb24cd95a529b441bcda0178057315dd2851e863dd9b1011a1281f03ad9d32b228d6c7759c88cf47a72405caf3fe7d8c67ae80899fb697f29a66e62db3fdbb1dd31167a3e4314d6589c838ce0c44f25698781203a83f152fbf63b08d5abd6567229d5529676c5523ca8f438b398f9bc1217745d7de7eb15177e62629882457177f41380f0b800f0ad241ce096325a0576b73c20f2bbb94df29b9f00b267bbab551c6b85bbab7a4a109a68051704f2aa0de3430b3763de5613fa2b53b1d0ab5c900f57e175b573c70d885026a4a556123e28138c9a74dcd60206a1dbf531971dcf494324ad6a9fe00a5a8fb5cd77f6c68e024825ba533746334d9d2a1b2f01675946b7cfd13f513d8d9d51430011573f73ee3b5705a3701f2e3b679e921d7cb1d4a440237f983a381ddd5f5edae5ea05966877911ada19d9595cbbd9d8715b85b7ee56f00729ad5811870459bc8a31915bed8784586b86fd5b2de43c7cef306b7961769606683d162f16dad43362c06b3b09d5714cdc5a039a2b8b66eddb9ddb9fba29860bb87c0abd296d4ebe04190bba3a0c1866a10574acd21bc9b9caf64ea154ea6075aeccae522b1639eae2adfb6ffa75ca446e1bd8e9ce0fd55f31cc4d14ce3385e2bfa169748870161882e1a2c2b7bd0754780fa8f75bf23a4ca4a24f70928f96b16fbcd
 * MD = 85e22d7d9a42f9244a38ee390da3dc3b682954a58625de6f6ff9fc431322ebba0f90605585e5dcb77a6bdfef3ac2a66e
 *
 * This vector stems from the "CAVP Testing: Secure Hashing" test vectors.
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bittestvectors.zip
 *
 * The message and digest from the test vector set are interpreted in little-endian order.
 *
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
sha384_test:
  /**
  * Set x10 to the desired KMAC_CFG.
  * x10 <= 0x6.
  * Bit  [   0] kmac_en   = 0x0
  * Bits [ 3:1] kstrength = 0x3 (L384)
  * Bits [ 5:4] mode      = 0x0 (SHA3)
  */
  li      x10, 0x6

  /* Set pointers to the SHA3-384 test vector. */
  la      x11, sha384_msg_len
  la      x12, sha384_msg
  la      x13, sha384_digest_len
  la      x14, sha384_rate
  la      x15, sha384_digest

  /* Run the test for the SHA3-384 test vector. */
  jal     x1,  run_kmac_test_vector

  ret

/**
 * Run a SHA3-512 test vector.
 *
 * Len = 0
 * Msg = 00
 * MD = a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26
 *
 * This vector stems from the "CAVP Testing: Secure Hashing" test vectors.
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bittestvectors.zip
 *
 * The message and digest from the test vector set are interpreted in little-endian order.
 *
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
sha512_test:
  /**
  * Set x10 to the desired KMAC_CFG.
  * x10 <= 0x8.
  * Bit  [   0] kmac_en   = 0x0
  * Bits [ 3:1] kstrength = 0x4 (L512)
  * Bits [ 5:4] mode      = 0x0 (SHA3)
  */
  li      x10, 0x8

  /* Set pointers to the SHA3-512 test vector. */
  la      x11, sha512_msg_len
  la      x12, sha512_msg
  la      x13, sha512_digest_len
  la      x14, sha512_rate
  la      x15, sha512_digest

  /* Run the test for the SHA3-512 test vector. */
  jal     x1,  run_kmac_test_vector

  ret

/**
 * Run a SHAKE-128 test vector.
 *
 * Len = 456
 * Msg = b212f7ef04ffcdcf72c39a6309486c0eeb390ff8f218d6bd978b976612f7f898c350e90bd130723e1126af69295019b4f52c06a629ab74e038
 * Output = e6684c673e7f126631a44a6ce2b1d717
 *
 * This vector stems from the "CAVP Testing: Secure Hashing" test vectors.
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/shakebytetestvectors.zip
 *
 * The message and digest from the test vector set are interpreted in little-endian order.
 *
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
shake128_test:
  /**
  * Set x10 to the desired KMAC_CFG.
  * x10 <= 0x20.
  * Bit  [   0] kmac_en   = 0x0
  * Bits [ 3:1] kstrength = 0x0 (L128)
  * Bits [ 5:4] mode      = 0x2 (SHAKE)
  */
  li      x10, 0x20

  /* Set pointers to the SHAKE-128 test vector. */
  la      x11, shake128_msg_len
  la      x12, shake128_msg
  la      x13, shake128_digest_len
  la      x14, shake128_rate
  la      x15, shake128_digest

  /* Run the test for the SHAKE-128 test vector. */
  jal     x1,  run_kmac_test_vector

  ret

/**
 * Run a SHAKE-256 test vector.
 *
 *
 * COUNT = 470
 * Outputlen = 768
 * Msg = dc886df3f69c49513de3627e9481db5871e8ee88eb9f99611541930a8bc885e0
 * Output = 00648afbc5e651649db1fd82936b00dbbc122fb4c877860d385c4950d56de7e096d613d7a3f27ed8f26334b0ccc1407b41dccb23dfaa529818d1125cd5348092524366b85fabb97c6cd1e6066f459bcc566da87ec9b7ba36792d118ac39a4cce
 *
 * This vector stems from the "CAVP Testing: Secure Hashing" test vectors.
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/shakebytetestvectors.zip
 *
 * The message and digest from the test vector set are interpreted in little-endian order.
 *
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
shake256_test:
  /**
  * Set x10 to the desired KMAC_CFG.
  * x10 <= 0x24.
  * Bit  [   0] kmac_en   = 0x0
  * Bits [ 3:1] kstrength = 0x2 (L256)
  * Bits [ 5:4] mode      = 0x2 (SHAKE)
  */
  li      x10, 0x24

  /* Set pointers to the SHAKE-256 test vector. */
  la      x11, shake256_msg_len
  la      x12, shake256_msg
  la      x13, shake256_digest_len
  la      x14, shake256_rate
  la      x15, shake256_digest

  /* Run the test for the SHAKE-256 test vector. */
  jal     x1,  run_kmac_test_vector

  ret

/**
 * Run a KMAC test vector.
 *
 * This routine allows to run any KMAC test vector by just setting
 * the KMAC_CFG and the test vector pointers.
 *
 * @param[in]     x10: KMAC_CFG
 * @param[in]     x11: Pointer to message length in bytes
 * @param[in]     x12: Message pointer
 * @param[in]     x13: Pointer to digest length in bytes (must be a multiple of 8)
 * @param[in]     x14: Pointer to keccak rate bytes
 * @param[in]     x15: Digest pointer
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
run_kmac_test_vector:
  /* Start the KMAC engine. */
  jal     x1,  kmac_start

  /* Let KMAC absorb the message. */
  jal     x1,  kmac_absorb

  /* Let KMAC process the message. */
  jal     x1,  kmac_process

  /* Squeeze the digest out of KMAC. */
  jal     x1,  kmac_squeeze

  /* Finish KMAC operation. */
  jal     x1,  kmac_finish

  ret

/**
 * Start the KMAC engine by issuing a start command.
 *
 * This routine does some additional checks on the KMAC CSRs.
 *
 * @param[in]     x10: KMAC_CFG
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
kmac_start:
  /* Set KMAC_CFG. */
  csrrw   x0,  KMAC_CFG, x10

  /* Clear KMAC_INTR.KMAC_ERROR. */
  li      x25, 1
  csrrw   x0,  KMAC_INTR, x25

  /* Poll KMAC_STATUS until SHA3 is in the IDLE state. */
  li      x25, 1
  li      x26, 1
  jal     x1,  poll_status

  /* Write the start command to KMAC_CMD. */
  li      x25, 0x1d
  csrrw   x0,  KMAC_CMD, x25

  /* Poll KMAC_STATUS until SHA3 is no longer in the IDLE state. */
  li      x25, 0
  li      x26, 1
  jal     x1,  poll_status

  /* Check if KMAC_INTR.KMAC_ERROR is 0. */
  csrrs   x22, KMAC_INTR, x0
  li      x25, 0
  jal     x1,  check_result_gpr

  ret

/**
 * Let KMAC absorb the message.
 *
 * This routine does some additional checks on the KMAC CSRs.
 *
 * @param[in]     x11: Pointer to message length in bytes
 * @param[in]     x12: Message pointer
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
kmac_absorb:
  /* Copy message len.
      x21 <= MEM(x11) */
  lw      x21, 0(x11)

  /* Set KMAC_BYTE_STROBE to all 1s. */
  addi    x25, x0, -1
  csrrw   x0,  KMAC_BYTE_STROBE, x25

_write_message_start:
  /* Check if we reached the last message chunk. */
  andi    x22, x21, 31
  li      x25, 1
  beq     x22, x21, _write_message_end

  /* Decrement message length. */
  addi    x21, x21, -32

  /* Set x25 to zero for the special case where msg len is 32
      and we need an all 1 mask. */
  li      x25, 0

  /* Check again if we reached the last message chunk. */
  beq     x21, x0,  _write_message_end

  /* Poll KMAC_IF_STATUS until MSG_WRITE_RDY is 1. */
  li      x25, 1
  li      x26, 1
  jal     x1,  poll_if_status

  /* Write the message chunk to KMAC_DATA. */
  li      x3, 22
  bn.lid  x3, 0(x12++)
  bn.wsrw KMAC_DATA_S0, w31
  bn.wsrw KMAC_DATA_S1, w22

  /* Send the msg to KMAC. */
  li      x25, 1
  csrrw   x0,  KMAC_MSG_SEND, x25

  /* Poll KMAC_IF_STATUS until MSG_WRITE_RDY is 1.
     This confirms to us the message has been sent to KMAC. */
  li      x25, 1
  li      x26, 1
  jal     x1,  poll_if_status

  /* Move to the next message chunk. */
  jal     x0, _write_message_start

_write_message_end:

  /* Set KMAC_BYTE_STROBE to 0x1. */
  sll     x25, x25, x21
  addi    x25, x25, -1
  csrrw   x0,  KMAC_BYTE_STROBE, x25

  /* Poll KMAC_IF_STATUS until MSG_WRITE_RDY is 1. */
  li      x25, 1
  li      x26, 1
  jal     x1,  poll_if_status

  /* Check if KMAC_IF_STATUS is 1. */
  csrrs   x22, KMAC_IF_STATUS, x0
  li      x25, 1
  jal     x1,  check_result_gpr

  /* Check if SHA3 is in the ABSORB state. */
  csrrs   x22, KMAC_STATUS, x0
  li      x25, 2
  jal     x1,  check_result_gpr

  /* Write the message to KMAC_DATA. */
  li      x3, 22
  bn.lid  x3, 0(x12)
  bn.wsrw KMAC_DATA_S0, w22
  bn.wsrw KMAC_DATA_S1, w31

  /* Send the msg to KMAC. */
  li      x25, 1
  csrrw   x0,  KMAC_MSG_SEND, x25

  ret

/**
 * Issue the process command.
 *
 * This routine does some additional checks on the KMAC CSRs.
 *
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
kmac_process:
  /* Poll KMAC_IF_STATUS until MSG_WRITE_RDY is 1.
     This confirms to us the message has been sent to KMAC. */
  li      x25, 1
  li      x26, 1
  jal     x1,  poll_if_status

  /* Clear KMAC_DATA to avoid overwriting the msg with the digest. */
  bn.wsrw KMAC_DATA_S0, w31
  bn.wsrw KMAC_DATA_S1, w31

  /* Write the process command to KMAC_CMD. */
  li      x25, 0x2e
  csrrw   x0,  KMAC_CMD, x25

  ret

/**
 * Squeeze the digest out of KMAC.
 *
 * This routine does some additional checks on the KMAC CSRs.
 *
 * @param[in]     x13: Pointer to digest length in bytes (must be a multiple of 8)
 * @param[in]     x14: Pointer to keccak rate bytes
 * @param[in]     x15: Digest pointer
 * @param[in]     x29: Max polling iterations
 * @param[in]     w31: All zero
 * @param[in/out]  w0: Test check pass counter
 */
kmac_squeeze:
  /* Load digest len.
      x20 <= MEM(x13) */
  lw      x20, 0(x13)

  /* Load keccak rate.
      x21 <= MEM(x14) */
  lw      x21, 0(x14)

  /* Set x25, x26 to the polling mask.
      We expect DIGEST_VALID to be true. */
  li      x25, 0x8
  li      x26, 0x8

  /* Zero out w30.
      w30 <= 0 */
  bn.xor  w30, w30, w30

  /* Set the word counter to 4.
      x4 <= 4 */
  addi    x4,  x0,  4

_read_digest_start:
  /* Stop reading the digest if the digest counter reaches 0. */
  beq     x20, x0,  _run_kmac_test_vector_finish

  /* Issue a run command if needed and
      update keccak rate counter accordingly. */
  jal     x1,  run_keccak

  /* Poll KMAC_IF_STATUS until DIGEST_VALID is high.
     This confirms to us the digest has been returned by KMAC. */
  jal     x1,  poll_if_status

  /* Check if KMAC_IF_STATUS has no errors and DIGEST_VALID is as expected. */
  csrrs   x22, KMAC_IF_STATUS, x0
  ori     x5,  x26, 0x7
  and     x22, x22, x5
  jal     x1,  check_result_gpr

  /* Read KMAC_DATA to receive the digest. */
  bn.wsrr w10, KMAC_DATA_S0
  bn.wsrr w11, KMAC_DATA_S1

  /* Unmask the digest. */
  bn.xor  w22, w10, w11

  /* Shift in the digest word. */
  bn.rshi  w30, w22, w30 >> 64

  /* Decrement the digest word counter. */
  addi     x4,  x4,  -1

  /* Skip writing the digest to memory if the word counter is not zero. */
  bne      x0,  x4,  _skip_write_digest

  /* Write the digest chunk to memory. */
  li       x3,  30
  bn.sid   x3,  0(x15++)

  /* Reset the digest word counter. */
  addi     x4,  x0,  4

  /* Zero out w30.
      w30 <= 0 */
  bn.xor  w30, w30, w30

_skip_write_digest:
  /* Update the digest and rate counters.
      x20 <= x20 - 8
      x21 <= x21 - 8 */
  addi    x20, x20, -8
  addi    x21, x21, -8

  /* Start the next iteration of the digest read loop. */
  jal     x0, _read_digest_start

_run_kmac_test_vector_finish:

  /* Skip writing the digest to memory if the word counter is equal to 4. */
  addi     x3,  x0,  4
  beq      x3,  x4,  _skip_write_digest_last

  /* Shift the last digest word to the LSB positions. */
  loop     x4,  1
    bn.rshi  w30, w31, w30 >> 64

  /* Write the digest chunk to memory. */
  li       x3,  30
  bn.sid   x3,  0(x15++)

_skip_write_digest_last:
  ret

/**
 * Finish KMAC operation by issuing a done command.
 */
kmac_finish:

  /* Write the done command to KMAC_CMD. */
  li      x9,  0x16
  csrrw   x0,  KMAC_CMD, x9

  ret

/**
 * Send Run command.
 *
 * @param[in] x14: Pointer to keccak rate bytes
 * @param[in] x21: keccak rate counter
 */
run_keccak:
  /* Return if the keccak rate has not been exhausted yet. */
  bne     x0,  x21, _run_keccak_return

  /* Write the run command to KMAC_CMD. */
  li      x9,  0x31
  csrrw   x0,  KMAC_CMD, x9

  /* Update the rate counter x21 += DMEM(x14) */
  lw      x9,  0(x14)
  add     x21, x21, x9

_run_keccak_return:
  ret

/**
 * Poll the KMAC_STATUS register until SHA3 is in the expected state.
 *
 * @param[in] x25: expected status
 * @param[in] x26: status mask
 * @param[in] x29: Max iterations
 */
poll_status:
  li      x28, 0
_poll_status_loop:
  beq     x28, x29, _poll_fail
  addi    x28, x28, 1
  csrrs   x22, KMAC_STATUS, x0
  and     x22, x22, x26
  beq     x22, x25, _poll_ret
  jal     x0, _poll_status_loop

/**
 * Poll the KMAC_IF_STATUS register until the KMAC-OTBN IF is in the expected state.
 *
 * @param[in] x25: expected IF-status
 * @param[in] x26: IF-status mask
 * @param[in] x29: Max iterations
 */
poll_if_status:
  li      x28, 0
_poll_if_status_loop:
  beq     x28, x29, _poll_fail
  addi    x28, x28, 1
  csrrs   x22, KMAC_IF_STATUS, x0
  and     x22, x22, x26
  beq     x22, x25, _poll_ret
  jal     x0, _poll_if_status_loop

_poll_fail:
  unimp

_poll_ret:
  ret

/**
 * Increment the error register if expected/actual results don't match.
 *
 * @param[in] w25: expected result
 * @param[in] w22: actual result
 * @param[in,out] w0: error count
 */
check_result_wdr:
  /* Increment error register if expected != actual. */
  bn.addi w1, w0, 1
  bn.cmp  w22, w25
  bn.sel  w0, w0, w1, Z

  ret

/**
 * Increment the error register if expected/actual results don't match.
 *
 * @param[in] x25: expected result
 * @param[in] x22: actual result
 * @param[in,out] w0: error count
 */
check_result_gpr:
  /* Skip the increment if the registers contain the same value. */
  beq     x22, x25, _check_result_gpr_ret
  /* Increment error register if actual != expected. */
  bn.addi w0, w0, 1

_check_result_gpr_ret:
  ret

.data

/**
 * SHA3-224 test vector.
 */
.balign 32
sha224_msg:
  .zero 64

.balign 4
sha224_msg_len:
  .zero 4

.balign 32
sha224_digest:
  .zero 32

.balign 4
sha224_digest_len:
  .zero 4

.balign 4
sha224_rate:
  .zero 4

/**
 * SHA3-256 test vector.
 */
.balign 32
sha256_msg:
  .zero 32

.balign 4
sha256_msg_len:
  .zero 4

.balign 32
sha256_digest:
  .zero 32

.balign 4
sha256_digest_len:
  .zero 4

.balign 4
sha256_rate:
  .zero 4

/**
 * SHA3-384 test vector.
 */
.balign 32
sha384_msg:
  .zero 960

.balign 4
sha384_msg_len:
  .zero 4

.balign 32
sha384_digest:
  .zero 64

.balign 4
sha384_digest_len:
  .zero 4

.balign 4
sha384_rate:
  .zero 4

/**
 * SHA3-512 test vector.
 */
.balign 32
sha512_msg:
  .zero 32

.balign 4
sha512_msg_len:
  .zero 4

.balign 32
sha512_digest:
  .zero 64

.balign 4
sha512_digest_len:
  .zero 4

.balign 4
sha512_rate:
  .zero 4

/**
 * SHAKE-128 test vector.
 */
.balign 32
shake128_msg:
  .zero 64

.balign 4
shake128_msg_len:
  .zero 4

.balign 32
shake128_digest:
  .zero 32

.balign 4
shake128_digest_len:
  .zero 4

.balign 4
shake128_rate:
  .zero 4

/**
 * SHAKE-256 test vector.
 */
.balign 32
shake256_msg:
  .zero 32

.balign 4
shake256_msg_len:
  .zero 4

.balign 32
shake256_digest:
  .zero 96

.balign 4
shake256_digest_len:
  .zero 4

.balign 4
shake256_rate:
  .zero 4
