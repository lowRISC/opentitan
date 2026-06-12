// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/nvm_info_field.h"

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/nvm_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/attestation.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.

/**
 * Partition 0, page 0 fields.
 */
const nvm_info_field_t kNvmInfoFieldLotName = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldLotNameStartOffset};

const nvm_info_field_t kNvmInfoFieldWaferNumber = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldWaferNumberStartOffset};

const nvm_info_field_t kNvmInfoFieldWaferXCoord = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldWaferXCoordStartOffset};

const nvm_info_field_t kNvmInfoFieldWaferYCoord = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldWaferYCoordStartOffset};

const nvm_info_field_t kNvmInfoFieldProcessData = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldProcessDataStartOffset};

const nvm_info_field_t kNvmInfoFieldAstCalibrationData = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldAstCalibrationDataStartOffset};

const nvm_info_field_t kNvmInfoFieldAstCfgVersion = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldAstCfgVersionStartOffset};

const nvm_info_field_t kNvmInfoFieldCpDeviceId = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldCpDeviceIdStartOffset};

const nvm_info_field_t kNvmInfoFieldAstIndividPatchAddr = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldAstIndividPatchAddrStartOffset};

const nvm_info_field_t kNvmInfoFieldAstIndividPatchVal = {
    .page = kNvmInfoPageFactoryId,
    .byte_offset = kNvmInfoFieldAstIndividPatchValStartOffset};

/**
 * Partition 0, page 1 fields.
 */
const nvm_info_field_t kNvmInfoFieldCreatorSeed = {
    .page = kNvmInfoPageCreatorSecret, .byte_offset = 0};

/**
 * Partition 0, page 2 fields.
 */
const nvm_info_field_t kNvmInfoFieldOwnerSeed = {
    .page = kNvmInfoPageOwnerSecret, .byte_offset = 0};

/**
 * Partition 0, page 3 fields.
 */
const nvm_info_field_t kNvmInfoFieldWaferAuthSecret = {
    .page = kNvmInfoPageWaferAuthSecret, .byte_offset = 0};

/**
 * Partition 0, page 4 fields.
 */
const nvm_info_field_t kNvmInfoFieldUdsAttestationKeySeed = {
    .page = kNvmInfoPageAttestationKeySeeds,
    .byte_offset = kNvmInfoFieldUdsKeySeedIdx * kAttestationSeedBytes};

const nvm_info_field_t kNvmInfoFieldCdi0AttestationKeySeed = {
    .page = kNvmInfoPageAttestationKeySeeds,
    .byte_offset = kNvmInfoFieldCdi0KeySeedIdx * kAttestationSeedBytes};

const nvm_info_field_t kNvmInfoFieldCdi1AttestationKeySeed = {
    .page = kNvmInfoPageAttestationKeySeeds,
    .byte_offset = kNvmInfoFieldCdi1KeySeedIdx * kAttestationSeedBytes};

const nvm_info_field_t kNvmInfoFieldTpmEkAttestationKeySeed = {
    .page = kNvmInfoPageAttestationKeySeeds,
    .byte_offset = kNvmInfoFieldTpmEkKeySeedIdx * kAttestationSeedBytes};

const nvm_info_field_t kNvmInfoFieldAttestationKeyGenVersion = {
    .page = kNvmInfoPageAttestationKeySeeds,
    .byte_offset = NVM_BYTES_PER_PAGE - 4u};

status_t manuf_nvm_info_field_read(nvm_info_field_t field, uint32_t *data_out,
                                   size_t num_words) {
  TRY(nvm_testutils_read_info_page(field.page, field.byte_offset, data_out,
                                   num_words));
  return OK_STATUS();
}

status_t manuf_nvm_info_field_write(nvm_info_field_t field, uint32_t *data_in,
                                    size_t num_words,
                                    bool erase_page_before_write,
                                    bool readback) {
  TRY(nvm_testutils_write_info_page(field.page, field.byte_offset, data_in,
                                    num_words, erase_page_before_write,
                                    readback));
  return OK_STATUS();
}
