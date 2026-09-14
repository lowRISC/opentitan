// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CHERIOT_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_TESTS_CHERIOT_MANIFEST_H_

/**
 * `manifest_t` layout, for the assembly that has to emit it by hand.
 *
 * `manifest.h` cannot be included from a CHERIoT translation unit - it reaches
 * `hardened.h`, which does not yet compile purecap - so these are spelled out
 * here instead. `cheriot_manifest_unittest.cc` checks each one
 * against the real struct on the host, so a layout change fails the build
 * rather than silently producing a bad image.
 */
#define MANIFEST_SIZE 1024
#define MANIFEST_ADDRESS_TRANSLATION_OFFSET 816
#define MANIFEST_VERSION_MINOR_OFFSET 824
#define MANIFEST_VERSION_MAJOR_OFFSET 826
#define MANIFEST_CODE_START_OFFSET 892
#define MANIFEST_CODE_END_OFFSET 896
#define MANIFEST_ENTRY_POINT_OFFSET 900

#define MANIFEST_VERSION_MINOR_1 0x6c47
#define MANIFEST_VERSION_MAJOR_2 0x0002

#endif  // OPENTITAN_SW_DEVICE_TESTS_CHERIOT_MANIFEST_H_
